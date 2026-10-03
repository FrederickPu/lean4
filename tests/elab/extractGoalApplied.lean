module

/-!
Suggestions of `extract_goal` from `extractGoal.lean`, applied: the extracted theorems, here proved,
and the closing tactics close the goals they were extracted from.
-/

theorem poly.goal.{u} (α : Type u) (x : α) : x = x := by
  rfl

theorem poly.{u} (α : Type u) (x : α) : x = x := by
  exact poly.goal α x

theorem relevant.goal (n : Nat) (hn : n = 1) : n = 1 := by
  exact hn

theorem relevant (n m k : Nat) (hn : n = 1) (hm : m = 2) : n = 1 := by
  exact relevant.goal n hn

theorem chosen.goal (n m : Nat) (hm : m = 2) : n = n := by
  rfl

theorem chosen (n m k : Nat) (hn : n = 1) (hm : m = 2) : n = n := by
  exact chosen.goal n m hm

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

def data.goal (n : Nat) : Fin (n + 1) :=
  0

def data (n : Nat) : Fin (n + 1) := by
  exact data.goal n

namespace Scoped
public def double (n : Nat) := n + n
scoped notation "⟪" n "⟫" => double n
end Scoped

open scoped Scoped in
theorem usesScoped.goal (n : Nat) : ⟪n⟫ = n + n := by
  rfl

open Scoped in
theorem usesScoped (n : Nat) : ⟪n⟫ = n + n := by
  exact usesScoped.goal n

section
local notation "dbl! " n:max => Scoped.double n

theorem usesLocal.goal (n : Nat) : dbl! n = n + n := by
  rfl

theorem usesLocal (n : Nat) : dbl! n = n + n := by
  exact usesLocal.goal n
end
