module

import Std.Tactic.Do

/-!
The suggestion of `extract_vcs` replaces the tactic with one closing tactic per goal, each on its
own line. The file elaborates after applying it.
-/

theorem womp : ∀ n : Nat, n + 0 = n ∧ 0 + n = n := by
  intro
  constructor
  extract_vcs
--^ codeAction
--^ codeActionApply: Extract 2 goals as theorems
--^ collectDiagnostics
