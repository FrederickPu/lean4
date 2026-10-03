module

/-!
`extract_goals` extracts every goal at once, with one closing tactic per goal. With `into M`,
`extract_goals` and `extract_goal` offer a code action that puts the theorems into the file of
module `M`.
-/

theorem both (n : Nat) : n + 0 = n ∧ 0 + n = n := by
  constructor
  extract_goals

/-! Goals with the same case tag get theorems with different names. -/

theorem sameTag (h : 1 = 1 → 2 = 2 → False) : False := by
  apply h
  extract_goals

/-! Each theorem keeps the hypotheses relevant to its goal, or all of them with `*`. -/

theorem relevant (n m : Nat) (h : m = 0) : n + 0 = n ∧ m = 0 := by
  constructor
  extract_goals

theorem all (n m : Nat) (h : m = 0) : n + 0 = n ∧ m = 0 := by
  constructor
  extract_goals *

/-! The message describes what the code action does to `M`'s file and to this one. -/

theorem intoFile (n : Nat) : n + 0 = n ∧ 0 + n = n := by
  constructor
  extract_goals into Example.VCs

theorem intoFileOne (n m : Nat) (h : m = 0) : n + 0 = n := by
  extract_goal h using addZero into Example.VCs
