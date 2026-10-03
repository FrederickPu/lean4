/-
Copyright (c) 2026 Frederick Pu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederick Pu
-/
module

prelude
public import Lean.Elab.Term
import Lean.Elab.Binders
import Lean.Elab.SyntheticMVars
import Init.While
import Lean.Meta.Tactic.ExposeNames
import Lean.PrettyPrinter
import Lean.PrettyPrinter.Delaborator.TopDownAnalyze
import Lean.Parser.Extension

public section

/-!
# Extracting goals as theorems

`extract` describes a goal as a theorem of its own, together with what to apply that theorem to in
order to close the goal. When a theorem with that statement exists already, it is used instead of a
new one. The resulting `Extraction` says nothing about where a new theorem ends up.
`Extraction.theoremSource?` and `Extraction.closingTactic` print it as source text, for whoever
writes that text into a file.
-/

namespace Lean.Elab.Tactic.Do.ExtractVC
open Meta

/-- A goal stated as a theorem of its own, and what to apply the theorem to in order to close it. -/
structure Extraction where
  /-- Name of the theorem. -/
  name        : Name
  /-- Universe parameters of the theorem. -/
  levelParams : List Name
  /-- Statement of the theorem: the goal's target under one binder per hypothesis. -/
  type        : Expr
  /--
  If the theorem is new, the source text that follows its name: universe parameters, a binder per
  leading `∀` of `type`, and the rest of `type` after a colon. It is checked to elaborate back to
  `type`. It is `none` if `name` is a theorem that exists already.
  -/
  signature?  : Option String
  /-- Whether a theorem named `name` exists already, but with a statement that this one replaces. -/
  restates    : Bool := false
  /-- The hypotheses to apply the theorem to, by the names they have after `expose_names`. -/
  args        : Array Name
  /-- Whether some of `args` only become accessible through `expose_names`. -/
  exposeNames : Bool

/-! ## Printing a signature that elaborates back -/

private def ppOptions (opts : Options) : Options :=
  opts
    -- Nothing may be elided.
    |> (pp.proofs.set · true)
    |> (pp.deepTerms.set · true)
    |> (pp.maxSteps.set · 1000000)
    -- Annotate what elaboration would not infer again.
    |> (pp.analyze.set · true)
    |> (pp.motives.all.set · true)
    |> (pp.letVarTypes.set · true)
    |> (pp.funBinderTypes.set · true)
    -- The theorem is elaborated outside of the goal's `open` declarations.
    |> (pp.fullNames.set · true)
    |> (pp.unicode.fun.set · true)

/-- Noisier than `ppOptions`, for statements on which `pp.analyze` falls short. -/
private def ppOptionsExplicit (opts : Options) : Options :=
  ppOptions opts
    |> (pp.explicit.set · true)
    |> (pp.analyze.typeAscriptions.set · true)
    |> (pp.analyze.explicitHoles.set · true)

/-- The signature of a theorem with universe parameters `lvls` that states `type`. -/
private def ppSignature (type : Expr) (lvls : List Name) : TermElabM String :=
  withoutModifyingEnv do
    -- `PrettyPrinter.ppSignature` prints declared constants, so declare one with this statement.
    let name := `_extractVC
    addDecl <| .axiomDecl { name, levelParams := lvls, type, isUnsafe := false }
    let sig := toString (← PrettyPrinter.ppSignature name).fmt
    return ((sig.dropPrefix? (toString name)).map (·.copy)).getD sig

/--
Whether `sig`, as the signature of a top-level theorem with universe parameters `lvls`, states
`type`. Only reducible definitions are unfolded, so that the text states what the goal showed rather
than something merely equivalent to it.
-/
private def roundtrips (type : Expr) (lvls : List Name) (sig : String) : TermElabM Bool := do
  let .ok cmd := Parser.runParserCategory (← getEnv) `command s!"theorem _extractVC{sig} := sorry"
    | return false
  let some declSig := cmd.find? (·.isOfKind ``Parser.Command.declSig) | return false
  -- The binders of `declSig`, then its type after `:`.
  let (binders, typeStx) := (declSig[0].getArgs, declSig[1][1])
  try
    -- Positions in `cmd` refer to `sig`, so its info nodes must not end up in the file's info tree.
    withEnableInfoTree false <| withLCtx {} {} <| Term.withLevelNames lvls <|
      Term.withoutAutoBoundImplicit <| Term.withoutErrToSorry do
        let e ← Term.elabBinders binders fun xs => do
          let e ← Term.elabType typeStx
          Term.synthesizeSyntheticMVarsNoPostponing
          mkForallFVars xs e
        let e ← instantiateMVars e
        if e.hasExprMVar || e.hasSorry then return false
        withNewMCtxDepth <| withReducible <| isDefEq e type
  catch _ => return false

/--
The signature of a theorem that states `type`, checked to elaborate back to `type`: with binders
before the colon where those print faithfully, and otherwise with a single `∀` after it.
-/
private def checkedSignature (type : Expr) (lvls : List Name) : TermElabM String := do
  let univs := if lvls.isEmpty then "" else ".{" ++ ", ".intercalate (lvls.map toString) ++ "}"
  -- `ppSignature` annotates binders less than `ppExpr` annotates the whole statement.
  let closed : TermElabM String := do return s!"{univs} : {← ppExpr type}"
  let mut sig := ""
  for opts in [ppOptions, ppOptionsExplicit] do
    for print in [ppSignature type lvls, closed] do
      sig ← withOptions opts print
      if ← roundtrips type lvls sig then return sig
  throwError "failed to print the goal so that it elaborates back. Best attempt:\n{sig}"

/-! ## Extraction -/

/--
The prefix of the names of theorems extracted from the goals of declaration `declName` in namespace
`ns`: the declaration's name, or `extracted` for declarations without a name of their own, such as
`example`.
-/
def theoremPrefix (declName ns : Name) : Name :=
  let declName := (privateToUserName declName).replacePrefix ns .anonymous
  ns ++ if declName.isInternal then `extracted else declName

/-- `<theoremPrefix>.<goal tag>`, the name for goal `g`. Untagged goals count as `goal`. -/
private def expectedName (g : MVarId) : TermElabM Name := do
  let some declName ← Term.getDeclName? | throwError "no enclosing declaration"
  let tag := (← g.getTag).eraseMacroScopes
  return theoremPrefix declName (← getCurrNamespace) ++ if tag.isAnonymous then `goal else tag

/-- `base`, with a numeric suffix if that is declared already or in `taken`. -/
private def freshName (base : Name) (taken : Array Name) : TermElabM Name := do
  let mut name := base
  let mut i := 1
  while taken.contains name || (← liftMacroM <| Macro.hasDecl name) do
    name := base.appendIndexAfter i
    i := i + 1
  return name

/--
A theorem among `candidates` that states `type`, up to reducible unfolding and the names of universe
parameters.
-/
def findTheorem? (type : Expr) (candidates : Array ConstantVal) : MetaM (Option Name) :=
  candidates.findSomeM? fun c => withNewMCtxDepth do
    let us ← c.levelParams.mapM fun _ => mkFreshLevelMVar
    let found ← withReducible <| isDefEq (c.instantiateTypeLevelParams us) type
    return if found then some c.name else none

/--
States goal `g` as a theorem over its hypotheses: one of `reusable` if it states exactly that, and
otherwise a new theorem with a name that is not in `taken`. Each hypothesis becomes an explicit
argument, except for dependent `let`s, which stay part of the statement. Leaves `g` as it is.

With `restate`, a theorem of `reusable` that has the name for `g` but a different statement is
restated, rather than avoided by a new name.
-/
def extract (g : MVarId) (taken : Array Name := #[]) (reusable : Array ConstantVal := #[])
    (restate := false) : TermElabM Extraction := g.withContext do
  let lctx ← getLCtx
  let exposed ← withExposedNames getLCtx
  let hyps := exposed.foldl (init := #[]) fun hyps h =>
    if h.isImplementationDetail then hyps else hyps.push h
  -- Explicit binders, so that the theorem takes every hypothesis by position.
  let exposed := hyps.foldl (init := exposed) fun lctx h =>
    if h.isLet (allowNondep := true) then lctx else lctx.setBinderInfo h.fvarId .default
  let type ← withLCtx exposed (← getLocalInstances) do
    instantiateMVars (← mkForallFVars (hyps.map (·.toExpr)) (← g.getType))
  if type.hasExprMVar then
    throwError "goal contains metavariables; supply invariants first\n\n{g}"
  if type.hasSorry then
    throwError "goal contains `sorry`, so it cannot be stated as a theorem\n\n{g}"
  unless ← isProp type do
    throwError "goal is not a proposition, so it cannot be stated as a theorem\n\n{g}"
  -- Universe metavariables become universe parameters, as they do for any declaration.
  let levelNames ← Term.getLevelNames
  let type := ((← getMCtx).levelMVarToParam (levelNames.elem ·) (fun _ => false) type).expr
  let levelParams := (collectLevelParams {} type).params.toList
  let args := hyps.filterMap fun h => if h.isLet then none else some h.userName
  let exposeNames := hyps.any fun h => h.userName != (lctx.get! h.fvarId).userName
  let base ← expectedName g
  -- Of the theorems with this statement, the one with the name for `g` comes first.
  if let some name ← findTheorem? type (reusable.filter (·.name == base) ++ reusable) then
    return { name, levelParams, type, signature? := none, args, exposeNames }
  let restates := restate && !taken.contains base && reusable.any (·.name == base)
  return {
    name := ← if restates then pure base else freshName base taken
    levelParams, type, args, exposeNames, restates
    signature? := some (← checkedSignature type levelParams)
  }

/--
Extracts each of `goals`, reusing `reusable` theorems where they fit. New theorems get distinct
names, and goals with the same statement share one.
-/
def extractAll (goals : List MVarId) (reusable : Array ConstantVal := #[]) (restate := false) :
    TermElabM (Array Extraction) :=
  goals.foldlM (init := #[]) fun extractions g => do
    let stated := extractions.filterMap fun e =>
      e.signature?.map fun _ => { name := e.name, levelParams := e.levelParams, type := e.type }
    let taken := extractions.map (·.name)
    return extractions.push (← extract g taken (reusable ++ stated) restate)

/-! ## Source text -/

namespace Extraction

/-- A new theorem's name and signature, as written inside namespace `ns`. -/
def headerSource? (e : Extraction) (ns : Name) : Option String :=
  (s!"{e.name.replacePrefix ns .anonymous}{·}") <$> e.signature?

/-- A new theorem with `sorry` for a proof, as it is written inside namespace `ns`. -/
def theoremSource? (e : Extraction) (ns : Name) : Option String :=
  (s!"theorem {·} := by\n  sorry") <$> e.headerSource? ns

/-- The tactic, on a single line, that closes the goal with the theorem inside namespace `ns`. -/
def closingTactic (e : Extraction) (ns : Name) : String :=
  let exact := e.args.foldl (init := s!"exact {e.name.replacePrefix ns .anonymous}")
    fun exact arg => s!"{exact} {arg}"
  if e.exposeNames then s!"expose_names; {exact}" else exact

end Extraction

end Lean.Elab.Tactic.Do.ExtractVC
