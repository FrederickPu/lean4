/-
Copyright (c) 2026 Frederick Pu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederick Pu
-/
module

prelude
public import Lean.Elab.Tactic.Basic
public import Lean.PrettyPrinter
import Init.Data.String.Defs
import Lean.PrettyPrinter.Delaborator.TopDownAnalyze
import Lean.Parser.Extension
import Lean.Server.CodeActions

public section

namespace Lean.Elab.Tactic
open Meta

/-- Data passed from `extract_vc` to its code action. -/
structure ExtractVCData where
  /-- Full text to insert above the enclosing command, including a trailing blank line. -/
  thmText   : String
  /-- Single-line replacement for the `extract_vc` call. -/
  closeText : String
  /-- Theorem name as it appears in `thmText`, for the code action title. -/
  relName   : String
  deriving TypeName

def vcPPOptions (opts : Options) : Options :=
  opts
    |> (pp.analyze.set · true)
    |> (pp.proofs.set · true)
    |> (pp.motives.all.set · true)
    |> (pp.unicode.fun.set · true)
    |> (pp.letVarTypes.set · true)
    |> (pp.deepTerms.set · true)
    |> (pp.maxSteps.set · 1000000)
    |> (pp.fullNames.set · true)
    |> (pp.funBinderTypes.set · true)

def vcPPOptionsExplicit (opts : Options) : Options :=
  vcPPOptions opts
    |> (pp.explicit.set · true)
    |> (pp.analyze.typeAscriptions.set · true)
    |> (pp.analyze.explicitHoles.set · true)

/-- A name component introduced by the elaborator, not a name the user wrote. -/
private def hasHiddenComponent : Name → Bool
  | .anonymous => false
  | .str p s => "_".isPrefixOf s || hasHiddenComponent p
  | .num p _ => hasHiddenComponent p

private def join (sep : String) (xs : Array String) : String :=
  String.intercalate sep xs.toList

/-- Re-elaborate `src` in an empty local context and test reducible defeq with `stmt`. -/
def roundtrips (stmt : Expr) (lvls : List Name) (src : String) : TermElabM Bool :=
  withoutModifyingState do
    let .ok stx := Parser.runParserCategory (← getEnv) `term src | return false
    try
      withLCtx {} {} <| Term.withLevelNames lvls <|
        Term.withoutAutoBoundImplicit <| Term.withoutErrToSorry do
          let e ← Term.elabType stx
          Term.synthesizeSyntheticMVarsNoPostponing
          let e ← instantiateMVars e
          if e.hasExprMVar || e.hasSorry then return false
          withNewMCtxDepth <| withReducible <| isDefEq e stmt
    catch _ => return false

private partial def freshenAux (env : Environment) (base : Name) (i : Nat) : Name :=
  let n := base.appendAfter s!"_{i}"
  if env.contains n then freshenAux env base (i + 1) else n

private def freshen (base : Name) : CoreM Name := do
  let env ← getEnv
  if env.contains base then return freshenAux env base 1 else return base

private partial def freshHypNameAux (lctx : LocalContext) (used : NameSet) (base : Name) (i : Nat) : Name :=
  let cand := base.appendIndexAfter i
  if lctx.usesUserName cand || used.contains cand then
    freshHypNameAux lctx used base (i + 1)
  else
    cand

private def freshHypName (lctx : LocalContext) (used : NameSet) (base : Name) : Name :=
  let base := base.eraseMacroScopes
  let base := if base.isAnonymous || hasHiddenComponent base then `h else base
  freshHypNameAux lctx used base 1

/--
Rename inaccessible hypotheses to fresh readable names.
The third component is every non-implementation-detail fvar, in context order.
The fourth is the names that become `exact` arguments: dependent lets stay inside the statement.
-/
private def prepareContext (lctx : LocalContext) :
    LocalContext × Array Name × Array Expr × Array Name := Id.run do
  let mut lctx := lctx
  let mut used : NameSet := {}
  let mut freshNames : Array Name := #[]
  let mut fvars : Array Expr := #[]
  let mut argNames : Array Name := #[]
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let mut name := decl.userName
    if name.hasMacroScopes then
      let fresh := freshHypName lctx used name
      lctx := lctx.setUserName decl.fvarId fresh
      used := used.insert fresh
      freshNames := freshNames.push fresh
      name := fresh
    else
      used := used.insert name
    -- `setBinderInfo` panics on lets. Nondep lets become explicit foralls in `mkForallFVars`.
    if decl.isLet (allowNondep := true) then
      fvars := fvars.push (mkFVar decl.fvarId)
      if decl.isNondep then
        argNames := argNames.push name
    else
      lctx := lctx.setBinderInfo decl.fvarId .default
      fvars := fvars.push (mkFVar decl.fvarId)
      argNames := argNames.push name
  return (lctx, freshNames, fvars, argNames)

@[builtin_tactic Lean.Parser.Tactic.extractVC]
def evalExtractVC : Tactic := fun _ => withMainContext do
  let some declName ← Term.getDeclName?
    | throwError "extract_vc: no enclosing declaration"
  let g ← getMainGoal
  let target ← instantiateMVars (← g.getType)
  if target.hasExprMVar then
    throwError "extract_vc: goal contains metavariables; supply invariants first"
  let lctx ← getLCtx
  let (lctx, freshNames, fvars, argNames) := prepareContext lctx
  let localInsts ← getLocalInstances
  withLCtx lctx localInsts do
    let stmt ← mkForallFVars fvars target (usedLetOnly := false) (generalizeNondepLet := true)
    let stmt ← instantiateMVars stmt
    if stmt.hasExprMVar then
      throwError "extract_vc: goal contains metavariables; supply invariants first"
    let lvls := (collectLevelParams {} stmt).params.toList
    let print (opts : Options → Options) : MetaM String :=
      withOptions opts <| return toString (← ppExpr stmt)
    let src ← print vcPPOptions
    let (ok, src) ←
      if ← roundtrips stmt lvls src then
        pure (true, src)
      else
        let src ← print vcPPOptionsExplicit
        pure (← roundtrips stmt lvls src, src)
    if !ok then
      logError m!"extract_vc: failed to round-trip the goal; no code action produced. Best attempt:\n{src}"
      return
    let userDecl := ((privateToUserName? declName).getD declName).eraseMacroScopes
    let ns ← getCurrNamespace
    let base :=
      if userDecl.isAnonymous || hasHiddenComponent userDecl then
        ns ++ `extracted
      else
        userDecl
    let goalName := (← g.getDecl).userName.eraseMacroScopes
    let goalName := if goalName.isAnonymous || hasHiddenComponent goalName then `goal else goalName
    let fullName ← freshen (base ++ goalName)
    let relName := fullName.replacePrefix (← getCurrNamespace) .anonymous
    let relNameStr := toString relName
    let univs :=
      if lvls.isEmpty then ""
      else ".{" ++ join ", " (lvls.toArray.map toString) ++ "}"
    let vis := if isPrivateName declName then "private " else ""
    let thmText := s!"{vis}theorem {relNameStr}{univs} : {src} := by\n  sorry\n\n"
    let args := join " " (argNames.map toString)
    let argSuffix := if args.isEmpty then "" else s!" {args}"
    let renames :=
      if freshNames.isEmpty then ""
      else s!"rename_i {join " " (freshNames.map toString)}; "
    let closeText := s!"{renames}exact {relNameStr}{argSuffix}"
    let data : ExtractVCData := { thmText, closeText, relName := relNameStr }
    pushInfoLeaf <| .ofCustomInfo { stx := ← getRef, value := .mk data }
    logInfo m!"extract_vc:\n{thmText}{closeText}"
    g.admit
    pruneSolvedGoals

end Lean.Elab.Tactic

end

namespace Lean.CodeAction
open Lean Elab Server Lsp RequestM

private def outermostCommand? (tree : InfoTree) (pos : String.Pos.Raw) : Option Syntax :=
  let best := tree.foldInfo (init := none) fun _ info (best : Option (Lean.Syntax.Range × Syntax)) =>
    match info, best with
    | .ofCommandInfo ci, best =>
      match ci.stx.getRange? with
      | some r =>
        if r.start ≤ pos && pos ≤ r.stop then
          match best with
          | none => some (r, ci.stx)
          | some (br, _) =>
            if r.start < br.start || (r.start == br.start && r.stop > br.stop) then
              some (r, ci.stx)
            else
              best
        else
          best
      | none => best
    | _, best => best
  best.map (·.2)

/-- Inserts the extracted theorem and replaces `extract_vc` with `exact <theorem>`. -/
@[builtin_code_action_provider]
def extractVCProvider : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  let startPos := doc.meta.text.lspPosToUtf8Pos params.range.start
  let endPos := doc.meta.text.lspPosToUtf8Pos params.range.end
  let hits := snap.infoTree.foldInfo (init := #[]) fun _ info acc => Id.run do
    let .ofCustomInfo { stx, value } := info | acc
    let some data := value.get? Tactic.ExtractVCData | acc
    let some range := stx.getRange? | acc
    unless range.start ≤ endPos && startPos ≤ range.stop do return acc
    acc.push (range, data)
  let mut actions : Array LazyCodeAction := #[]
  for (tacRange, data) in hits do
    let some cmdStx := outermostCommand? snap.infoTree tacRange.start | continue
    let some cmdStart := cmdStx.getPos? | continue
    let lspStart := doc.meta.text.utf8PosToLspPos cmdStart
    let insertPos := { lspStart with character := 0 }
    let tacLsp := doc.meta.text.utf8RangeToLspRange tacRange
    actions := actions.push {
      eager := {
        title := s!"Extract goal as theorem {data.relName}"
        kind? := "refactor.extract"
        isPreferred? := some true
        edit? := some <| .ofTextDocumentEdit {
          textDocument := doc.versionedIdentifier
          edits := #[
            { range := { start := insertPos, «end» := insertPos }, newText := data.thmText },
            { range := tacLsp, newText := data.closeText }
          ]
        }
      }
    }
  return actions

end Lean.CodeAction
