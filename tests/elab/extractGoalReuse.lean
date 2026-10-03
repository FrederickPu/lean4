module

/-!
`extract_goal` and `extract_goals` close a goal with a theorem that states it already, instead of
suggesting a new one.
-/

/-! A theorem extracted earlier for the same declaration is used again. -/

theorem taken.goal : True := trivial

theorem taken : True := by
  extract_goal

/-! If it states something else, the new theorem gets another name. -/

theorem clash.goal : 1 = 1 := rfl

theorem clash : True := by
  extract_goal

/-! The theorem named with `using` is used if it states the goal. -/

theorem chosenName : True := trivial

theorem usesIt : True := by
  extract_goal using chosenName

/-! Goals with the same statement share one theorem. -/

theorem twice : True ∧ True := by
  constructor
  extract_goals

/-! With `into M`, any theorem of `M` that states the goal is used. -/

theorem addZero (n : Nat) : n + 0 = n := by
  extract_goals into Init.Core
