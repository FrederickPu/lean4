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
import Lean.Meta.Instances
import Lean.Meta.Tactic.Cleanup
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
`Extraction.declSource?` and `Extraction.closingTactic` print it as source text, for whoever
writes that text into a file.
-/

namespace Lean.Elab.Tactic.ExtractGoal
open Meta

/-- Which hypotheses of a goal its theorem takes. -/
inductive Hypotheses where
  /-- All of them. -/
  | all
  /--
  Those that the goal depends on, and propositions about them, as `MVarId.cleanup` selects them;
  all of them if the goal is `False`.
  -/
  | relevant
  /-- These, and those that they or the goal depend on. -/
  | only (fvarIds : Array FVarId)

/--
The signature of a declaration as source text, checked to elaborate back to the declaration's type,
and what that text needs from its surroundings in order to do so.
-/
structure Signature where
  /--
  What follows the declaration's name: universe parameters, a binder per leading `∀` of the type,
  and the rest of the type after a colon.
  -/
  text        : String
  /--
  The namespaces whose scoped syntax or instances `text` relies on, which must be open where the
  declaration is stated.
  -/
  scopes      : Array Name
  /--
  Whether `text` uses syntax that is local to the current file, such as a `local notation`, so that
  the declaration can only be stated there.
  -/
  localSyntax : Bool

/--
A goal stated as a theorem of its own, or as a definition if it is not a proposition, and what to
apply that declaration to in order to close the goal.
-/
structure Extraction where
  /-- Name of the declaration. -/
  name        : Name
  /-- Universe parameters of the declaration. -/
  levelParams : List Name
  /-- Its type: the goal's target under one binder per hypothesis that it takes. -/
  type        : Expr
  /-- Whether `type` is a proposition, so that the declaration is a theorem. -/
  isProp      : Bool
  /-- The signature of the declaration if it is new, and `none` if `name` is an existing theorem. -/
  signature?  : Option Signature
  /-- Whether a theorem named `name` exists already, but with a statement that this one replaces. -/
  restates    : Bool := false
  /-- The hypotheses to apply the declaration to, by the names they have after `expose_names`. -/
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

/-- The signature of a declaration with universe parameters `lvls` and type `type`. -/
private def ppSignature (type : Expr) (lvls : List Name) : TermElabM String :=
  withoutModifyingEnv do
    -- `PrettyPrinter.ppSignature` prints declared constants, so declare one with this type.
    let name := `_extractGoal
    addDecl <| .axiomDecl { name, levelParams := lvls, type, isUnsafe := false }
    let sig := toString (← PrettyPrinter.ppSignature name).fmt
    return ((sig.dropPrefix? (toString name)).map (·.copy)).getD sig

/--
`sig`, parsed, if as the signature of a top-level declaration with universe parameters `lvls` it
states `type`. Only reducible definitions are unfolded, so that the text states what the goal showed
rather than something merely equivalent to it.
-/
private def elaboratesBack? (type : Expr) (lvls : List Name) (sig : String) :
    TermElabM (Option Syntax) := do
  let src := s!"theorem _extractGoal{sig} := sorry"
  let .ok cmd := Parser.runParserCategory (← getEnv) `command src | return none
  let some declSig := cmd.find? (·.isOfKind ``Parser.Command.declSig) | return none
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
        if e.hasExprMVar || e.hasSorry then return none
        let ok ← withNewMCtxDepth <| withReducible <| isDefEq e type
        return if ok then some declSig else none
  catch _ => return none

/-! ### What a signature relies on -/

/-- The namespaces whose scoped entries are active in `env`, through `open` or `namespace`. -/
def activeNamespaces (env : Environment) : NameSet :=
  match (Parser.parserExtension.ext.getState (asyncMode := .local) env).stateStack with
  | top :: _ => top.activeScopes
  | [] => {}

/-- The kinds of the syntax nodes of `stx`. -/
private def syntaxKinds (stx : Syntax) : NameSet := Id.run do
  let mut kinds : NameSet := {}
  for stx in stx.topDown do
    kinds := kinds.insert stx.getKind
  return kinds

/--
The open namespaces whose scoped entries a declaration with the parsed signature `sig` and type
`type` relies on: scoped syntax that `sig` uses, and scoped instances that `type` refers to.
-/
private def scopedNamespaces (sig : Syntax) (type : Expr) : CoreM (Array Name) := do
  let env ← getEnv
  let kinds := syntaxKinds sig
  let consts := type.getUsedConstantsAsSet
  let parsers := Parser.parserExtension.ext.getState (asyncMode := .local) env
  let insts := Meta.instanceExtension.ext.getState (asyncMode := .local) env
  let usesSyntax (ns : Name) := parsers.scopedEntries.map.find? ns |>.any (·.any fun
    | .kind k | .parser _ k .. => kinds.contains k
    | _ => false)
  let usesInstance (ns : Name) := insts.scopedEntries.map.find? ns |>.any (·.any fun e =>
    e.globalName?.any consts.contains)
  return (activeNamespaces env).toList.toArray.filter fun ns => usesSyntax ns || usesInstance ns

/--
Whether the parsed signature `sig` uses syntax that is local to the current file: a parser of some
syntax category that is declared in this file but is not among the entries that the file exports.
-/
private def usesLocalSyntax (sig : Syntax) : CoreM Bool := do
  let env ← getEnv
  let parsers := Parser.parserExtension.ext.getState (asyncMode := .local) env
  let some top := parsers.stateStack.head? | return false
  let exported : NameSet := parsers.newEntries.foldl (init := {}) fun exported e =>
    match e with
    | .global (.parser _ k _) | .scoped _ (.parser _ k _) => exported.insert k
    | _ => exported
  return (syntaxKinds sig).toList.any fun k =>
    env.contains k && (env.getModuleIdxFor? k).isNone && !exported.contains k &&
      top.state.categories.foldl (fun found _ cat => found || cat.kinds.contains k) false

/-! ### The checked signature -/

/--
The signature of a declaration of type `type`, checked to elaborate back to `type`: with binders
before the colon where those print faithfully, and otherwise with a single `∀` after it.
-/
private def checkedSignature (type : Expr) (lvls : List Name) : TermElabM Signature := do
  let univs := if lvls.isEmpty then "" else ".{" ++ ", ".intercalate (lvls.map toString) ++ "}"
  -- `ppSignature` annotates binders less than `ppExpr` annotates the whole statement.
  let closed : TermElabM String := do return s!"{univs} : {← ppExpr type}"
  let mut text := ""
  for opts in [ppOptions, ppOptionsExplicit] do
    for print in [ppSignature type lvls, closed] do
      text ← withOptions opts print
      if let some stx ← elaboratesBack? type lvls text then
        let scopes ← scopedNamespaces stx type
        return { text, scopes, localSyntax := ← usesLocalSyntax stx }
  throwError "failed to print the goal so that it elaborates back. Best attempt:\n{text}"

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

private def isTaken (name : Name) (taken : Array Name) : TermElabM Bool :=
  return taken.contains name || (← liftMacroM <| Macro.hasDecl name)

/-- `base`, with a numeric suffix if that is declared already or in `taken`. -/
private def freshName (base : Name) (taken : Array Name) : TermElabM Name := do
  let mut name := base
  let mut i := 1
  while ← isTaken name taken do
    name := base.appendIndexAfter i
    i := i + 1
  return name

/-- The hypotheses of `g` that `hyps` selects, or `none` for all of them. -/
private def selectHypotheses (g : MVarId) (hyps : Hypotheses) : MetaM (Option LocalContext) := do
  let cleanedUp (cleanup : MetaM MVarId) := withoutModifyingState do
    return some (← (← cleanup).getDecl).lctx
  match hyps with
  | .all => return none
  | .relevant =>
    -- Every hypothesis may matter for a contradiction.
    if (← instantiateMVars (← g.getType)).consumeMData.isConstOf ``False then return none
    cleanedUp g.cleanup
  | .only fvarIds => cleanedUp (g.cleanup fvarIds (indirectProps := false))

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
States goal `g` as a theorem over the hypotheses that `hyps` selects: one of `reusable` if it states
exactly that, and otherwise a new theorem. Each hypothesis becomes an explicit argument, except for
dependent `let`s, which stay part of the statement. Leaves `g` as it is.

The theorem is named `name?`, in full, or else gets a name for `g` that is not in `taken`. With
`restate`, a theorem of `reusable` that has that name but a different statement is restated, rather
than avoided by another name. A goal that is not a proposition becomes a new definition.
-/
def extract (g : MVarId) (hyps : Hypotheses := .relevant) (name? : Option Name := none)
    (taken : Array Name := #[]) (reusable : Array ConstantVal := #[]) (restate := false) :
    TermElabM Extraction := g.withContext do
  let lctx ← getLCtx
  let selected? ← selectHypotheses g hyps
  let exposed ← withExposedNames getLCtx
  let kept := exposed.foldl (init := #[]) fun kept h =>
    if h.isImplementationDetail || !(selected?.all (·.contains h.fvarId)) then kept
    else kept.push h
  -- Explicit binders, so that the theorem takes every hypothesis by position.
  let exposed := kept.foldl (init := exposed) fun lctx h =>
    if h.isLet (allowNondep := true) then lctx else lctx.setBinderInfo h.fvarId .default
  let type ← withLCtx exposed (← getLocalInstances) do
    instantiateMVars (← mkForallFVars (kept.map (·.toExpr)) (← g.getType))
  if type.hasExprMVar then
    throwError "goal contains metavariables, so it cannot be stated as a theorem\n\n{g}"
  if type.hasSorry then
    throwError "goal contains `sorry`, so it cannot be stated as a theorem\n\n{g}"
  -- Universe metavariables become universe parameters, as they do for any declaration.
  let levelNames ← Term.getLevelNames
  let type := ((← getMCtx).levelMVarToParam (levelNames.elem ·) (fun _ => false) type).expr
  let levelParams := (collectLevelParams {} type).params.toList
  let isProp ← isProp type
  let args := kept.filterMap fun h => if h.isLet then none else some h.userName
  let exposeNames := kept.any fun h => h.userName != (lctx.get! h.fvarId).userName
  let base ← name?.getDM (expectedName g)
  if isProp then
    -- Of the theorems with this statement, the one with the name for `g` comes first.
    let named := reusable.filter (·.name == base)
    if let some name ← findTheorem? type (if name?.isSome then named else named ++ reusable) then
      return { name, levelParams, type, isProp, signature? := none, args, exposeNames }
  let restates := restate && isProp && !taken.contains base && reusable.any (·.name == base)
  let name ← if restates then pure base else match name? with
    | none => freshName base taken
    | some name => do
      if ← isTaken name taken then
        let what := if isProp then " and does not state the goal" else ""
        throwError "`{name}` has already been declared{what}"
      pure name
  return {
    name, levelParams, type, isProp, args, exposeNames, restates
    signature? := some (← checkedSignature type levelParams)
  }

/--
Extracts each of `goals`, reusing `reusable` theorems where they fit. New declarations get distinct
names, and goals with the same statement share one.
-/
def extractAll (goals : List MVarId) (hyps : Hypotheses := .relevant)
    (reusable : Array ConstantVal := #[]) (restate := false) : TermElabM (Array Extraction) :=
  goals.foldlM (init := #[]) fun extractions g => do
    let stated := extractions.filterMap fun e => do
      guard (e.isProp && e.signature?.isSome)
      return { name := e.name, levelParams := e.levelParams, type := e.type }
    let taken := extractions.map (·.name)
    return extractions.push (← extract g hyps none taken (reusable ++ stated) restate)

/-! ## Source text -/

namespace Extraction

/-- A new declaration's name and signature, as written inside namespace `ns`. -/
def headerSource? (e : Extraction) (ns : Name) : Option String :=
  (s!"{e.name.replacePrefix ns .anonymous}{·.text}") <$> e.signature?

/--
A new declaration with `sorry` for its value, as it is written inside namespace `ns` where the
namespaces `opened` are open. `isPublic` makes it `public`.
-/
def declSource? (e : Extraction) (ns : Name) (opened : NameSet := {}) (isPublic := false) :
    Option String :=
  e.signature?.map fun sig =>
    let scopes := sig.scopes.filter (!opened.contains ·)
    let openIn := if scopes.isEmpty then "" else
      s!"open scoped {" ".intercalate (scopes.map toString).toList} in\n"
    let header := s!"{e.name.replacePrefix ns .anonymous}{sig.text}"
    let decl :=
      if e.isProp then s!"theorem {header} := by\n  sorry" else s!"def {header} :=\n  sorry"
    openIn ++ (if isPublic then "public " else "") ++ decl

/-- The tactic, on one line, that closes the goal with the declaration inside namespace `ns`. -/
def closingTactic (e : Extraction) (ns : Name) : String :=
  let exact := e.args.foldl (init := s!"exact {e.name.replacePrefix ns .anonymous}")
    fun exact arg => s!"{exact} {arg}"
  if e.exposeNames then s!"expose_names; {exact}" else exact

end Extraction

end Lean.Elab.Tactic.ExtractGoal
