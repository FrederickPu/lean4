/-
Copyright (c) 2026 Frederick Pu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederick Pu
-/
module

prelude
public import Lean.Elab.Tactic.Basic
public import Lean.Elab.Tactic.Do.ExtractVC.Basic
public import Std.Tactic.Do.Syntax
import Lean.Meta.Tactic.TryThis
import Lean.Server.CodeActions
import Lean.Parser.Module
meta import Lean.Parser.Module

public section

/-!
# `extract_vc` and `extract_vcs`

These tactics extract goals as theorems (see `ExtractVC.extract`), admit the goals, and offer an
edit that adds the theorems to a file and closes the goals with them:

* By default the theorems go above the enclosing command, and the edit is a "Try this" suggestion.
  A tactic does not get to see where that command starts, so the suggestion is made once the
  command has been elaborated.
* `extract_vcs into M` puts them into the file of module `M` instead, creating it if needed. An
  edit of several files is beyond a "Try this" suggestion, so this one is a code action.
-/

namespace Lean.Elab.Tactic.Do.ExtractVC

/-- The extractions of one tactic call, in the order of the goals it admitted. -/
private structure Recorded where
  extractions : Array Extraction
  /-- The module whose file the theorems go into, or `none` for the current file. -/
  into?       : Option Name
  deriving TypeName

/-- The closing tactics, one per line, lined up at `column`. -/
private def closers (extractions : Array Extraction) (ns : Name) (column : Nat) : String :=
  ("\n".pushn ' ' column).intercalate (extractions.map (·.closingTactic ns)).toList

private def intoTitle (extractions : Array Extraction) (into : Name) : String :=
  let goals := s!"{extractions.size} goal{if extractions.size == 1 then "" else "s"}"
  if extractions.all (·.signature?.isNone) then s!"Close {goals} with theorems of {into}"
  else s!"Extract {goals} into {into}"

/-! ## Tactics -/

/--
The theorems that may already state the goals: those of module `into`, or else those extracted
earlier in the current file for the same declaration.
-/
private def reusableTheorems (into? : Option Name) : TacticM (Array ConstantVal) := do
  let env ← getEnv
  match into? with
  | some into =>
    let some idx := env.getModuleIdx? into | return #[]
    return env.header.moduleData[idx]!.constants.filterMap fun c => do
      -- Inside a module, the theorems of another module come without proofs, as axioms.
      guard (c.isTheorem || c.isAxiom)
      guard (!c.name.isInternal && !isPrivateName c.name)
      return c.toConstantVal
  | none =>
    let some declName ← Term.getDeclName? | return #[]
    let pre := theoremPrefix declName (← getCurrNamespace)
    let consts ← env.getLocalConstantInfos (skipTheoremSubDecls := true)
    return consts.filterMap fun c => do
      let name := privateToUserName c.name
      guard (c.kind == .thm && pre.isPrefixOf name && c.name != declName)
      return { c.sig.get with name }

/-- Extracts `goals`, records the extractions at `ref`, and admits the goals. -/
private def extractGoals (ref : Syntax) (goals : List MVarId) (into? : Option Name := none) :
    TacticM Unit := do
  if goals.isEmpty then throwNoGoalsToBeSolved
  let reusable ← reusableTheorems into?
  -- Abstracting the hypotheses and elaborating the printed statements must not touch the proof.
  let extractions ← withoutModifyingState <| extractAll goals reusable (restate := into?.isSome)
  pushInfoLeaf <| .ofCustomInfo { stx := ref, value := .mk { extractions, into? : Recorded } }
  if let some into := into? then
    let lines (texts : Array String) := indentD ("\n".intercalate texts.toList)
    let added := extractions.filter (!·.restates) |>.filterMap (·.theoremSource? .anonymous)
    let restated := extractions.filter (·.restates) |>.filterMap (·.headerSource? .anonymous)
    let adds := if added.isEmpty then m!"" else m!" adds to {into}:{lines added}\nand"
    let restates := if restated.isEmpty then m!"" else
      m!" restates in {into}, keeping their proofs:{lines restated}\nand"
    logInfo m!"The code action \"{intoTitle extractions into}\"{adds}{restates} replaces \
      `extract_vcs` with:{indentD (closers extractions (← getCurrNamespace) 0)}"
  goals.forM (·.admit)
  pruneSolvedGoals

@[builtin_tactic Lean.Parser.Tactic.extractVC]
def evalExtractVC : Tactic := fun ref => do
  extractGoals ref [← getMainGoal]

@[builtin_tactic Lean.Parser.Tactic.extractVCs]
def evalExtractVCs : Tactic := fun ref => do
  let into? := match ref with
    | `(tactic| extract_vcs into $into:ident) => some into.getId
    | _ => none
  extractGoals ref (← getUnsolvedGoals) into?

/-! ## Suggestion in the current file -/

open Command Meta.Tactic.TryThis in
/--
Suggests the edit for the extractions recorded while elaborating `cmd`, one suggestion per tactic
call. It is a single replacement reaching from the start of `cmd` to the end of the tactic: the
theorems, the source in between as it was, and the closing tactics.

This runs as a linter because linters are what runs after a command with the whole command at hand.
-/
private def suggestExtractions : Linter where
  run cmd := do
    let isExtract (stx : Syntax) :=
      stx.isOfKind ``Lean.Parser.Tactic.extractVC || stx.isOfKind ``Lean.Parser.Tactic.extractVCs
    unless (cmd.find? isExtract).isSome do return
    let some cmdStart := cmd.getPos? | return
    let text ← getFileMap
    let ns ← getCurrNamespace
    for tree in ← getInfoTrees do
      let recorded := tree.foldInfo (init := #[]) fun _ info recorded => Id.run do
        let .ofCustomInfo { stx, value } := info | recorded
        let some { extractions, into? := none } := value.get? Recorded | recorded
        recorded.push (stx, extractions)
      for (tac, extractions) in recorded do
        let some tacRange := tac.getRange? | continue
        let thms := (extractions.filterMap (·.theoremSource? ns)).toList
        let unchanged := String.Pos.Raw.extract text.source cmdStart tacRange.start
        let close := closers extractions ns (text.toPosition tacRange.start).column
        let title :=
          match extractions with
          | #[{ name, signature? := some _, .. }] =>
            s!"Extract goal as theorem {name.replacePrefix ns .anonymous}"
          | #[{ name, signature? := none, .. }] =>
            s!"Close goal with theorem {name.replacePrefix ns .anonymous}"
          | _ => s!"Extract {extractions.size} goals as theorems"
        -- Without new theorems, only the tactic changes.
        let (span, edit, footer) :=
          if thms.isEmpty then (tacRange, close, MessageData.nil)
          else
            (⟨cmdStart, tacRange.stop⟩, s!"{"\n\n".intercalate thms}\n\n{unchanged}{close}",
              m!"\nand above the declaration:{indentD ("\n".intercalate thms)}")
        liftCoreM <| addSuggestion tac (origSpan? := Syntax.ofRange span) (footer := footer)
          { suggestion := edit
            -- Lines after the first go below the first, which follows `[apply] `.
            messageData? := some <| .nest 8 (closers extractions ns 0)
            toCodeActionTitle? := some fun _ => title }

builtin_initialize addLinter suggestExtractions

/-! ## Code action for `extract_vcs into` -/

/--
The URI of the source file of module `mod`, given that `uri` is that of module `main`: both files
are under the directory that is one level up from `uri` per component of `main`.
-/
private def sourceUri (uri : String) (main mod : Name) : String :=
  let parent (uri : String) := uri.toSlice.dropEndWhile (· != '/') |>.dropEnd 1 |>.copy
  let root := Nat.repeat parent (max 1 main.components.length) uri
  root ++ "/" ++ "/".intercalate (mod.components.map toString) ++ ".lean"

/-- The header of the source text `src`, and where it ends. -/
private def parseHeader (src : String) : IO (TSyntax ``Parser.Module.header × String.Pos.Raw) := do
  let (header, _, _) ← Parser.parseHeader (Parser.mkInputContext src "<input>")
  return (header, header.raw.getTailPos?.getD 0)

private def isModuleHeader : TSyntax ``Parser.Module.header → Bool
  | `(Parser.Module.header| module $[prelude]? $_*) => true
  | _ => false

open Server RequestM in
/--
The range of the name and signature of theorem `name` in `src`, the source of the module that
declares it.
-/
private def headerRange? (snap : Snapshots.Snapshot) (src : String) (name : Name) :
    RequestM (Option Lsp.Range) := do
  let some ranges ← runCoreM snap (findDeclarationRanges? name) | return none
  let text := FileMap.ofString src
  let start := text.ofPosition ranges.range.pos
  let decl := String.Pos.Raw.extract src start (text.ofPosition ranges.range.endPos)
  let .ok decl := Parser.runParserCategory snap.env `command decl | return none
  let some first := decl.find? (·.isOfKind ``Parser.Command.declId) >>= (·.getPos?) | return none
  let some last := decl.find? (·.isOfKind ``Parser.Command.declSig) >>= (·.getTailPos?)
    | return none
  let shift (pos : String.Pos.Raw) : String.Pos.Raw := ⟨start.byteIdx + pos.byteIdx⟩
  return text.utf8RangeToLspRange ⟨shift first, shift last⟩

open Server RequestM in
/--
For `extract_vcs into M` under the cursor: adds the new theorems to the end of the file of `M`,
creating it with the imports of the current file if needed, restates the theorems whose statement
changed, makes the current file import `M`, and replaces the tactic with the closing tactics.
-/
@[builtin_code_action_provider]
private def intoFileProvider : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  let text := doc.meta.text
  let cursor := text.lspRangeToUtf8Range params.range
  let recorded := snap.infoTree.foldInfo (init := #[]) fun ctx info recorded => Id.run do
    let .ofCustomInfo { stx, value } := info | recorded
    let some { extractions, into? := some into } := value.get? Recorded | recorded
    let some range := stx.getRange? | recorded
    unless range.start ≤ cursor.stop && cursor.start ≤ range.stop do return recorded
    recorded.push (ctx.currNamespace, range, extractions, into)
  if recorded.isEmpty then return #[]
  let (header, headerEnd) ← parseHeader text.source
  let env := snap.env
  recorded.mapM fun (ns, tacRange, extractions, into) => do
    let uri := sourceUri doc.meta.uri env.mainModule into
    let existing? ← match System.Uri.fileUriToPath? uri with
      | some file => do if ← file.pathExists then some <$> IO.FS.readFile file else pure none
      | none => pure none
    let isModule ← match existing? with
      | some src => (isModuleHeader ·.1) <$> parseHeader src
      | none => pure (isModuleHeader header)
    let thms := "\n\n".intercalate <| extractions.toList.filterMap fun e => do
      guard !e.restates
      return (if isModule then "public " else "") ++ (← e.theoremSource? .anonymous)
    let mut changes : Array Lsp.DocumentChange := #[]
    match existing? with
    | some src =>
      let mut edits : Array Lsp.TextEdit := #[]
      for e in extractions do
        if let (true, some header) := (e.restates, e.headerSource? .anonymous) then
          if let some range ← headerRange? snap src e.name then
            edits := edits.push { range, newText := header }
      unless thms.isEmpty do
        let theEnd := (FileMap.ofString src).utf8PosToLspPos src.rawEndPos
        let sep := if src.endsWith "\n" then "\n" else "\n\n"
        edits := edits.push { range := ⟨theEnd, theEnd⟩, newText := s!"{sep}{thms}\n" }
      unless edits.isEmpty do
        changes := changes.push <| .edit { textDocument := { uri, version? := none }, edits }
    | none =>
      unless thms.isEmpty do
        -- The new file imports what the current one does, so that the statements elaborate there.
        let imports := env.imports.map (·.module) |>.filter (· != `Init) |>.toList.eraseDups
        let importKw := if isModule then "public import" else "import"
        let fileHeader := (if isModule then "module\n\n" else "") ++
          String.join (imports.map (s!"{importKw} {·}\n")) ++
          "\n-- The hypotheses are each goal's whole context; proofs rarely use all of them.\n\
          set_option linter.unusedVariables false\n"
        changes := changes.push (.create { uri, options? := some { ignoreIfExists := true } })
        let start : Lsp.Position := ⟨0, 0⟩
        changes := changes.push <| .edit {
          textDocument := { uri, version? := none }
          edits := #[{ range := ⟨start, start⟩, newText := s!"{fileHeader}\n{thms}\n" }] }
    let mut edits : Array Lsp.TextEdit := #[]
    unless env.imports.any (·.module == into) do
      let pos := text.utf8PosToLspPos headerEnd
      edits := edits.push {
        range := ⟨pos, pos⟩
        newText := if headerEnd == 0 then s!"import {into}\n" else s!"\nimport {into}" }
    edits := edits.push {
      range := text.utf8RangeToLspRange tacRange
      newText := closers extractions ns (text.toPosition tacRange.start).column }
    changes := changes.push <| .edit { textDocument := doc.versionedIdentifier, edits }
    return {
      eager.title := intoTitle extractions into
      eager.kind? := "refactor.extract"
      eager.isPreferred? := true
      eager.edit? := some { documentChanges? := changes }
    }

end Lean.Elab.Tactic.Do.ExtractVC
