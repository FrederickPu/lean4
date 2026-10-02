# `extract_vc`: extract the current goal into a top-level theorem

## Goal

A tactic `extract_vc`, used inside a proof (typically after `mvcgen`), that offers a
one-click edit which:

1. inserts `theorem womp.vc1 : <statement> := by sorry` directly above the enclosing
   declaration `womp` (above its docstring and attributes), and
2. replaces the `extract_vc` call with a tactic that closes the goal using the new
   theorem.

The theorem name is `<enclosing decl name>.<goal userName>`, e.g. `womp.vc1`.

Hard requirement: **the inserted statement must round-trip.** It has to re-elaborate to
the original goal. We never insert text that hasn't been checked.

## Architecture

The work is split into two halves:

| Part | Runs | Responsibility |
|---|---|---|
| `extract_vc` tactic | elaboration time (`TacticM`) | compute name, statement text, closing text; verify round-trip; store result in a custom info node; admit the goal |
| code action | language server (`RequestM`) | find the stored result, find the enclosing command's range, emit a `WorkspaceEdit` with two `TextEdit`s |

Why not "Try this" (`Lean.Meta.Tactic.TryThis.addSuggestion`): it applies a single
`TextEdit` at the tactic's own range, and `TacticM` does not expose the enclosing
command's syntax/position. A Batteries tactic code action gets the syntax stack (so the
command's exact start, including modifiers) and can return a multi-edit `WorkspaceEdit`.

An infoview button (custom widget) can be added later, reusing the same stored data
(see "Later steps").

## Data passed from tactic to code action

```lean
structure ExtractVCData where
  /-- Full text to insert above the command, including trailing blank line. -/
  thmText   : String
  /-- Single-line replacement for the `extract_vc` call. -/
  closeText : String
  deriving TypeName
```

Stored with:

```lean
pushInfoLeaf <| .ofCustomInfo { stx := (← getRef), value := .mk data }
```

`closeText` is kept on one line (`rename_i a b; exact womp.vc1 x a b`) so the
replacement needs no indentation handling.

## Tactic: `extract_vc`

```lean
syntax (name := extractVC) "extract_vc" : tactic
```

Steps, all inside `withMainContext`:

### 1. Names

```lean
let some declName ← Term.getDeclName? | throwError "extract_vc: no enclosing declaration"
let declName := (privateToUserName? declName).getD declName
let goalName := (← g.getDecl).userName.eraseMacroScopes
let goalName := if goalName.isAnonymous then `goal else goalName
let fullName := declName ++ goalName                                    -- Foo.womp.vc1
let relName  := fullName.replacePrefix (← getCurrNamespace) .anonymous  -- womp.vc1
```

- Collision: if `(← getEnv).contains fullName`, append `_1`, `_2`, …
- Declaring `womp.vc1` before `womp` exists is allowed.
- `example` / auto-named instances: `getDeclName?` yields an internal name. Fall back to
  a fixed base (e.g. `extracted`) or refuse with a clear error.

### 2. Preconditions

- `let target ← instantiateMVars (← g.getType)`
- If `target.hasExprMVar`, error: *"goal contains metavariables; supply invariants
  first"*.
- SPred-shaped goals (`P ⊢ₛ Q`) are allowed but produce ugly lemmas. Document that
  users should run `mleave` first.

### 3. Context and binder names

- Collect fvars: every `LocalDecl` in the goal's context with
  `!decl.isImplementationDetail`, in context order.
- Inaccessible hypotheses (`decl.userName.hasMacroScopes`, shown as `h✝`) get fresh,
  readable names (`h_1`, `h_2`, …, avoiding clashes) via `LocalContext.setUserName`,
  and the work continues under `withLCtx` with the renamed context.
- Record the fresh names, in context order, for the `rename_i` in the closing tactic.
  (`rename_i` renames the most recent inaccessible hypotheses in order. Since we rename
  *all* of them, the lists line up.)

### 4. Statement

```lean
let stmt ← mkForallFVars fvars target
let lvls := (collectLevelParams {} stmt).params.toList
```

The statement is printed as **one closed term** (`∀ (x : α) (h : p x), target`), so the
exact text we insert is the exact text we check. Binders-before-colon can come later
(see "Later steps").

### 5. Pretty-printing options

Merged from our round-trip requirements and CanonicalDrafter's `applyOptions`:

```lean
def vcPPOptions (opts : Options) : Options := opts |>
  (pp.analyze.set · true) |>
  (pp.proofs.set · true) |>          -- otherwise proofs print as `⋯`
  (pp.motives.all.set · true) |>     -- match/recursor motives; VCs contain elaborated matches
  (pp.unicode.fun.set · true) |>     -- cosmetic (`↦`)
  (pp.letVarTypes.set · true) |>     -- `let x : T := v`; do-block VCs keep lets
  (pp.deepTerms.set · true) |>       -- otherwise deep subterms print as `⋯`
  (pp.maxSteps.set · 1000000) |>     -- avoid truncation on large VCs
  (pp.fullNames.set · true) |>       -- immune to `open … in` / namespace scope
  (pp.funBinderTypes.set · true)
```

```lean
let src := toString (← withOptions vcPPOptions (ppExpr stmt))
```

If a typed accessor doesn't resolve on the toolchain (`pp.analyze` lives in
`TopDownAnalyze` and has moved before), use `opts.setBool `pp.analyze true` for that
entry.

### 6. Round-trip check

`pp.analyze` is best-effort, so it is backed by an explicit check on the **string**:

```lean
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
```

Design choices:

- `withoutModifyingState`: failed attempts leak no messages or mvar assignments.
- `withoutErrToSorry`: elaboration errors throw instead of being logged and replaced
  with `sorry`.
- Empty `LCtx`: the inserted theorem cannot see the proof's hypotheses.
- Reducible transparency: default-transparency defeq could accept a statement that is
  only equal after unfolding, i.e. a lemma that works but states something different
  from what the user saw.

Escalation on failure:

1. retry with `pp.explicit` added (noisy but robust), and optionally
   `pp.analyze.typeAscriptions` / `pp.analyze.explicitHoles` if they exist on the
   toolchain (check with `#help option pp.analyze`);
2. if every attempt fails: `logError` with the best attempt, **store no data** (so no
   code action appears), and leave the goal unchanged.

### 7. Build texts, store, admit

```lean
let univs := if lvls.isEmpty then "" else ".{" ++ ", ".intercalate (lvls.map toString) ++ "}"
let thmText := s!"theorem {relName}{univs} : {src} := by\n  sorry\n\n"
let args    := " ".intercalate (fvarUserNames.map toString)   -- after renaming
let renames := if freshNames.isEmpty then "" else s!"rename_i {" ".intercalate freshNames}; "
let closeText := s!"{renames}exact {relName} {args}"
```

- Universes are always listed explicitly (`womp.vc1.{u}`), never left to auto-bound
  implicits (Mathlib-style projects disable them).
- Names in `args` may need `«»` escaping. Use `Name.toString` (which escapes) rather
  than raw string components.

Then:

1. `pushInfoLeaf` with `ExtractVCData` (see above);
2. `logInfo m!"extract_vc: {thmText}"`, so the text is visible and testable with
   `#guard_msgs`;
3. `g.admit`, so the file still elaborates (with the usual `sorry` warning) until the
   user clicks.

## Code action

Registered with Batteries' `@[tactic_code_action extractVC]` (`Batteries.CodeAction`).

> **Verify first:** the exact `TacticCodeAction` signature and the order of the syntax
> stack against `Batteries/CodeAction/Attr.lean` and an existing tactic code action in
> Batteries on the pinned toolchain. The outline below is intentionally API-light.

Outline:

1. In the info tree node handed to the action, find the `CustomInfo` whose
   `value.get? ExtractVCData` is `some data` and whose `stx` is this tactic.
   No data → return `#[]` (round-trip failed or tactic errored).
2. Take the **outermost** syntax in the stack: the whole command, including docstring,
   attributes, modifiers, and any `open … in` / `set_option … in` wrapper.
3. Insertion point: column 0 of the line containing the command's start position
   (`doc.meta.text.utf8PosToLspPos`).
4. Return one `LazyCodeAction` titled `Extract goal as theorem {relName}`, marked
   preferred, whose `WorkspaceEdit` contains:
   - insert `data.thmText` at the insertion point;
   - replace the `extract_vc` token's range with `data.closeText`.

Both edits go in the same `TextDocumentEdit` (same document version), so the editor
applies them atomically and positions are interpreted against the pre-edit text.

## Edge cases

| Case | Handling |
|---|---|
| Unassigned invariants / any mvars | error, ask user to supply invariants |
| Inaccessible hyps (`h✝`) | rename to fresh names; `rename_i` in closing text |
| Universe params | explicit `.{u, v}` on the new theorem |
| `open … in` / `set_option … in` | insert above the outermost wrapper; `pp.fullNames` keeps names valid |
| Section `variable`s | appear as fvars → become explicit binders *and* auto-included section vars. v1: accept the shadowing; later: detect and skip section fvars |
| Name collision on re-run | numeric suffix |
| `private` decls | strip private prefix for naming; consider emitting `private theorem` |
| `where` / auxiliary decls | `getDeclName?` gives e.g. `womp.foo` → `womp.foo.vc1` (fine) |
| `example` | fallback base name or refuse |
| Huge VCs | `pp.analyze` is slow; acceptable for an on-demand tactic, but avoid in `all_goals` loops until `extract_vcs` exists |

## Testing

- **Regression file** of mvcgen examples: loop with invariant, `StateT` + `ExceptT`,
  early `return`, nested `match`, goals with inaccessible hyps, universe-polymorphic
  programs, decl inside a namespace and inside `open … in`.
- **Tactic output** via `#guard_msgs` on the `logInfo` text. This pins down naming,
  binder renaming, universes, and printed statements.
- **Round-trip** for each regression case: paste the generated theorem into a test file
  and check it elaborates, and that `closeText` closes the original goal. (This
  duplicates the built-in check deliberately, catching bugs in the check itself.)
- **Code action / click, from the command line.** `tests/server_interactive` directive
  `codeActionApply: <title substring>` is the click. It requests `textDocument/codeAction`
  at the cursor (the same actions as the lightbulb and as a suggestion's `[apply]` button,
  including `Try this` library-suggestion tactics and `extract_vc`), applies that
  `WorkspaceEdit` with `didChange`, and can be followed by `sync` / `collectDiagnostics` /
  `goals`. Edits are applied from the end of the file so ranges stay valid.
  `codeAction` (no apply) still snapshots the edit JSON. A manual VS Code check remains
  useful, but it is not the regression path.
- Any round-trip failure in the regression file is a printer bug: work around it
  (another pp option) or report upstream.

## Later steps

1. `extract_vcs`: all goals in one action, one combined `WorkspaceEdit`.
2. Binders before the colon (`theorem womp.vc1 (x : α) (h : p x) : target`). Re-check by
   parsing `∀ <binders>, <type>`, which elaborates identically to the signature.
3. Relevance-based context cleanup (Mathlib `extract_goal` default) with a `*` toggle
   for "all hypotheses".
4. Infoview button: a widget that receives the two edits (plus the command position,
   recomputed server-side) and calls `applyEdit`.
5. Skip section-variable fvars.

## To verify on the pinned toolchain before coding

- [ ] mvcgen goal `userName`s (format of `vcN` / `invN`, any hierarchical names)
- [ ] `TacticCodeAction` signature and syntax-stack order in Batteries
- [ ] typed accessors for every option in `vcPPOptions` (esp. `pp.analyze`)
- [ ] `pp.analyze.*` sub-option names (`#help option pp.analyze`)
- [ ] `Term.withoutErrToSorry`, `Term.withLevelNames`, `withLCtx` signatures
