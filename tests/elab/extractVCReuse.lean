module

import Std.Tactic.Do

/-!
`extract_vc` and `extract_vcs` close a goal with a theorem that states it already, instead of
suggesting a new one.
-/

/-! A theorem extracted earlier for the same declaration is used again. -/

theorem taken.goal : True := trivial

theorem taken : True := by
  extract_vc

/-! If it states something else, the new theorem gets another name. -/

theorem clash.goal : 1 = 1 := rfl

theorem clash : True := by
  extract_vc

/-! Goals with the same statement share one theorem. -/

theorem twice : True ∧ True := by
  constructor
  extract_vcs

/-! With `into M`, any theorem of `M` that states the goal is used. -/

theorem addZero (n : Nat) : n + 0 = n := by
  extract_vcs into Init.Core
