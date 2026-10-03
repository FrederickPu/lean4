/-
Copyright (c) 2026 Frederick Pu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederick Pu
-/
module

prelude
public import Lean.Elab.Tactic.ElabTerm
public import Lean.Elab.Tactic.ExtractGoal.Basic
import Lean.Meta.Tactic.TryThis
import Lean.Server.CodeActions
import Lean.Parser.Module
meta import Lean.Parser.Module

public section

/-!
# `extract_goal` and `extract_goals`

These tactics extract goals as theorems (see `ExtractGoal.extract`), admit the goals, and offer an
edit that adds the theorems to a file and closes the goals with them:

* By default the theorems go above the enclosing command, and the edit is a "Try this" suggestion.
  A tactic does not get to see where that command starts, so the suggestion is made once the
  command has been elaborated.
* With `into M`, they go into the file of module `M` instead, which is created if needed. An edit
  of several files is beyond a "Try this" suggestion, so this one is a code action.
-/

namespace Lean.Elab.Tactic.ExtractGoal

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
earlier in the current file for the same declaration, and theorem `name?`.
-/
private def reusableTheorems (into? name? : Option Name) : TacticM (Array ConstantVal) := do
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
    let declName? ← Term.getDeclName?
    let pre? ← declName?.mapM fun declName => return theoremPrefix declName (← getCurrNamespace)
    -- Theorem `name?` of an imported module, which may come as an axiom.
    let imported := (name? >>= env.find?).filter (fun c => c.isTheorem || c.isAxiom)
    let consts ← env.getLocalConstantInfos (skipTheoremSubDecls := true)
    return imported.toArray.map (·.toConstantVal) ++ consts.filterMap fun c => do
      -- Inside a module, theorems that are not `public` have private names.
      let name := privateToUserName c.name
      guard (c.kind == .thm && some c.name != declName?)
      guard (name? == some name || pre?.any (·.isPrefixOf name))
      return { c.sig.get with name }

/--
Extracts `goals`, keeping the hypotheses that `hyps` selects, records the extractions at `ref`, and
admits the goals. A single goal may be given the name `name?`.
-/
private def extractGoals (ref : Syntax) (goals : List MVarId) (hyps : Hypotheses)
    (name? into? : Option Name) : TacticM Unit := do
  if goals.isEmpty then throwNoGoalsToBeSolved
  let reusable ← reusableTheorems into? name?
  let restate := into?.isSome
  -- Abstracting the hypotheses and elaborating the printed statements must not touch the proof.
  let extractions ← withoutModifyingState do
    match goals, name? with
    | [g], some name => return #[← extract g hyps name #[] reusable restate]
    | _, _ => extractAll goals hyps reusable restate
  if let (some into, some e) := (into?, extractions.find? (·.signature?.any (·.localSyntax))) then
    throwError "cannot state `{e.name}` in `{into}`, since its statement uses notation that is \
      local to this file:{indentD ((e.headerSource? .anonymous).getD "")}"
  pushInfoLeaf <| .ofCustomInfo { stx := ref, value := .mk { extractions, into? : Recorded } }
  if let some into := into? then
    let lines (texts : Array String) := indentD ("\n".intercalate texts.toList)
    let added := extractions.filter (!·.restates) |>.filterMap (·.declSource? .anonymous)
    let restated := extractions.filter (·.restates) |>.filterMap (·.headerSource? .anonymous)
    let adds := if added.isEmpty then m!"" else m!" adds to {into}:{lines added}\nand"
    let restates := if restated.isEmpty then m!"" else
      m!" restates in {into}, keeping their proofs:{lines restated}\nand"
    logInfo m!"The code action \"{intoTitle extractions into}\"{adds}{restates} replaces \
      `{ref[0].getAtomVal}` with:{indentD (closers extractions (← getCurrNamespace) 0)}"
  goals.forM (·.admit)
  pruneSolvedGoals

@[builtin_tactic Lean.Parser.Tactic.extractGoal]
def evalExtractGoal : Tactic := fun stx => do
  let `(tactic| extract_goal $hyps $[using $name?]? $[into $into?]?) := stx
    | throwUnsupportedSyntax
  let hyps ← match hyps with
    | `(Lean.Parser.Tactic.extractGoalHyps| *) => pure .all
    | `(Lean.Parser.Tactic.extractGoalHyps| $[$ids:ident]*) =>
      if ids.isEmpty then pure .relevant else .only <$> getFVarIds (ids.map (·.raw))
    | _ => throwUnsupportedSyntax
  let name? ← name?.mapM fun name => return (← getCurrNamespace) ++ name.getId
  extractGoals stx [← getMainGoal] hyps name? (into?.map (·.getId))

@[builtin_tactic Lean.Parser.Tactic.extractGoals]
def evalExtractGoals : Tactic := fun stx => do
  let `(tactic| extract_goals $[*%$all?]? $[into $into?]?) := stx | throwUnsupportedSyntax
  let hyps := if all?.isSome then .all else .relevant
  extractGoals stx (← getUnsolvedGoals) hyps none (into?.map (·.getId))

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
      [``Lean.Parser.Tactic.extractGoal, ``Lean.Parser.Tactic.extractGoals].contains stx.getKind
    unless (cmd.find? isExtract).isSome do return
    let some cmdStart := cmd.getPos? | return
    let text ← getFileMap
    let ns ← getCurrNamespace
    -- The theorems are stated where the command is, outside of its `open … in`.
    let opened := activeNamespaces (← getEnv)
    for tree in ← getInfoTrees do
      let recorded := tree.foldInfo (init := #[]) fun _ info recorded => Id.run do
        let .ofCustomInfo { stx, value } := info | recorded
        let some { extractions, into? := none } := value.get? Recorded | recorded
        recorded.push (stx, extractions)
      for (tac, extractions) in recorded do
        let some tacRange := tac.getRange? | continue
        let decls := (extractions.filterMap (·.declSource? ns opened)).toList
        let unchanged := String.Pos.Raw.extract text.source cmdStart tacRange.start
        let close := closers extractions ns (text.toPosition tacRange.start).column
        let title :=
          match extractions with
          | #[{ name, isProp, signature? := some _, .. }] =>
            let kind := if isProp then "theorem" else "definition"
            s!"Extract goal as {kind} {name.replacePrefix ns .anonymous}"
          | #[{ name, signature? := none, .. }] =>
            s!"Close goal with theorem {name.replacePrefix ns .anonymous}"
          | _ => s!"Extract {extractions.size} goals as theorems"
        -- Without new declarations, only the tactic changes.
        let (span, edit, footer) :=
          if decls.isEmpty then (tacRange, close, MessageData.nil)
          else
            (⟨cmdStart, tacRange.stop⟩, s!"{"\n\n".intercalate decls}\n\n{unchanged}{close}",
              m!"\nand above the declaration:{indentD ("\n".intercalate decls)}")
        liftCoreM <| addSuggestion tac (origSpan? := Syntax.ofRange span) (footer := footer)
          { suggestion := edit
            -- Lines after the first go below the first, which follows `[apply] `.
            messageData? := some <| .nest 8 (closers extractions ns 0)
            toCodeActionTitle? := some fun _ => title }

builtin_initialize addLinter suggestExtractions

/-! ## Code action for `into` -/

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

private def hasImports : TSyntax ``Parser.Module.header → Bool
  | `(Parser.Module.header| $[module]? $[prelude]? $imports*) => !imports.isEmpty
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
For `extract_goal into M` or `extract_goals into M` under the cursor: adds the new theorems to the
end of the file of `M`, creating it with the imports of the current file if needed, restates the
theorems whose statement changed, makes the current file import `M`, and replaces the tactic with
the closing tactics.
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
    let decls := "\n\n".intercalate <| extractions.toList.filterMap fun e => do
      guard !e.restates
      e.declSource? .anonymous (isPublic := isModule)
    let mut changes : Array Lsp.DocumentChange := #[]
    match existing? with
    | some src =>
      let mut edits : Array Lsp.TextEdit := #[]
      for e in extractions do
        if let (true, some header) := (e.restates, e.headerSource? .anonymous) then
          if let some range ← headerRange? snap src e.name then
            edits := edits.push { range, newText := header }
      unless decls.isEmpty do
        let theEnd := (FileMap.ofString src).utf8PosToLspPos src.rawEndPos
        let sep := if src.endsWith "\n" then "\n" else "\n\n"
        edits := edits.push { range := ⟨theEnd, theEnd⟩, newText := s!"{sep}{decls}\n" }
      unless edits.isEmpty do
        changes := changes.push <| .edit { textDocument := { uri, version? := none }, edits }
    | none =>
      unless decls.isEmpty do
        -- The new file imports what the current one does, so that the statements elaborate there.
        let imports := env.imports.map (·.module) |>.filter (· != `Init) |>.toList.eraseDups
        let importKw := if isModule then "public import" else "import"
        let blocks := [
          if isModule then "module" else "",
          "\n".intercalate (imports.map (s!"{importKw} {·}")),
          "-- Proofs of extracted goals rarely use all of their hypotheses.\n\
          set_option linter.unusedVariables false",
          decls]
        changes := changes.push (.create { uri, options? := some { ignoreIfExists := true } })
        let start : Lsp.Position := ⟨0, 0⟩
        changes := changes.push <| .edit {
          textDocument := { uri, version? := none }
          edits := #[{
            range := ⟨start, start⟩
            newText := "\n\n".intercalate (blocks.filter (· != "")) ++ "\n" }] }
    let mut edits : Array Lsp.TextEdit := #[]
    unless env.imports.any (·.module == into) do
      let pos := text.utf8PosToLspPos headerEnd
      edits := edits.push {
        range := ⟨pos, pos⟩
        newText :=
          if headerEnd == 0 then s!"import {into}\n"
          else if hasImports header then s!"\nimport {into}" else s!"\n\nimport {into}" }
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

end Lean.Elab.Tactic.ExtractGoal
