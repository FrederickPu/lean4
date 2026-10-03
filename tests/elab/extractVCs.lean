module

import Std.Tactic.Do

/-!
`extract_vcs` extracts every goal at once, with one closing tactic per goal. With `into M`, it offers
a code action that puts the theorems into the file of module `M`.
-/

theorem both (n : Nat) : n + 0 = n ∧ 0 + n = n := by
  constructor
  extract_vcs

/-! Goals with the same case tag get theorems with different names. -/

theorem sameTag (h : 1 = 1 → 2 = 2 → False) : False := by
  apply h
  extract_vcs

/-! The message describes what the code action does to `M`'s file and to this one. -/

theorem intoFile (n : Nat) : n + 0 = n ∧ 0 + n = n := by
  constructor
  extract_vcs into Example.VCs
