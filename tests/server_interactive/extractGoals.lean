module

/-!
The suggestion of `extract_goals` replaces the tactic with one closing tactic per goal, each on its
own line. The file elaborates after applying it.
-/

theorem womp : ∀ n : Nat, n + 0 = n ∧ 0 + n = n := by
  intro
  constructor
  extract_goals
--^ codeAction
--^ codeActionApply: Extract 2 goals as theorems
--^ collectDiagnostics
