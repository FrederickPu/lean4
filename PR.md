feat: add `extract_goal` and `extract_goals` tactics

This PR adds the tactics `extract_goal` and `extract_goals`, which turn the main goal, or every goal, into a theorem of its own with one click: the click edits the file, inserting the theorem and replacing the tactic with a proof of the goal by that theorem. With `into M`, the click writes the theorems into the file of module `M` instead, which separates the verification conditions that `vcgen` produces from the program proof.

Mathlib's `extract_goal` prints the goal as a theorem and leaves the rest to the user: copy the text, paste it somewhere, hope that it elaborates, and rewrite the proof to use it. Here the click does all of that. It turns

```lean
theorem womp : ∀ n : Nat, n + 0 = n := by
  intro
  extract_goal
```

into

```lean
theorem womp.goal (n : Nat) : n + 0 = n := by
  sorry

theorem womp : ∀ n : Nat, n + 0 = n := by
  intro
  expose_names; exact womp.goal n
```

The statement is checked to elaborate back to the goal before the edit is offered, so the inserted theorem states exactly the goal. The forms of Mathlib's tactic (`*`, hypothesis names, `using name`) are kept.

This matters now that core has `vcgen`. `vcgen` reduces the correctness proof of a program to verification conditions: several goals, each with a long context about the program's state, and each usually a fact about numbers or lists rather than about the program. Proving them inline buries the program proof under that reasoning, and every change to the program produces them anew. Verifiers such as Verus, Why3 and Frama-C keep such obligations apart from the code for this reason. `extract_goals into M` gives `vcgen` that workflow with ordinary Lean declarations. One click moves all conditions into a module of their own, each as a standalone theorem that a person or an automated prover can work on, and leaves the correctness proof as `vcgen` followed by one `exact` per condition:

```lean
  vcgen [mySum] invariants
  · fun _pref suff acc => ⌜acc + suff.sum = l.sum⌝
  exact mySum_correct.vc1 l r h
  expose_names; exact mySum_correct.vc2 l r h a h_1
  expose_names; exact mySum_correct.vc3 l r h pref cur suff _h b h_1
```

After the program changes, running `extract_goals into M` again reuses the theorems that still state a goal, restates in place those that changed while keeping their proofs, and adds only what is new, so that only the conditions that changed need attention.

The edit in the current file comes from a linter hook, because a tactic cannot see where its enclosing command starts, and `into M` is a code action, because it edits two files. The server test runner gains a `codeActionApply` directive to test such edits.

Unlike Mathlib's tactic, this one admits the goal. Mathlib's `extract_goal` should be removed when Mathlib adopts this, since both parse the same input.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
