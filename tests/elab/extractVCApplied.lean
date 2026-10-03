module

import Std.Tactic.Do

/-!
Suggestions of `extract_vc` from `extractVC.lean`, applied: the extracted theorems, here proved, and
the closing tactics close the goals they were extracted from.
-/

theorem poly.goal.{u} (α : Type u) (x : α) : x = x := by
  rfl

theorem poly.{u} (α : Type u) (x : α) : x = x := by
  exact poly.goal α x

theorem splitNat.succ (n : Nat) : n + 1 = n + 1 := by
  rfl

theorem splitNat (n : Nat) : n = n := by
  cases n
  · rfl
  · expose_names; exact splitNat.succ n

theorem shadowed.goal (x_1 : Nat) (x : x_1 = 1) : True := by
  trivial

theorem shadowed (x : Nat) (x : x = 1) : True := by
  expose_names; exact shadowed.goal x_1 x
