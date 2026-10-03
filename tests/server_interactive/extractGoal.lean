module

/-!
The suggestion of `extract_goal` inserts the extracted theorem above the enclosing command, which
includes its docstring, its attributes and `open … in`. The file elaborates after applying it.
-/

open Nat in
/-- doc -/
@[simp] theorem womp : ∀ n : Nat, n + 0 = n := by
  intro
  extract_goal
--^ codeAction
--^ codeActionApply: Extract goal as theorem
--^ collectDiagnostics
