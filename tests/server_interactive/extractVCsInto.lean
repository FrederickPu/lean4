module

import Std.Tactic.Do

/-!
`extract_vcs into M` offers a code action that creates the file of module `M` with the imports of
this file and the extracted theorems, makes this file import `M`, and replaces the tactic with one
closing tactic per goal.
-/

theorem womp : ∀ n : Nat, n + 0 = n ∧ 0 + n = n := by
  intro
  constructor
  extract_vcs into Example.VCs
--^ codeAction
