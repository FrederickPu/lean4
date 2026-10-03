module

import Std.Tactic.Do

/-!
What `extract_vc` suggests: the theorem it extracts from the main goal, and the tactic that closes
the goal with it.
-/

/-! The theorem is named after the enclosing declaration and the goal's case tag. -/

theorem womp : True := by
  extract_vc

example : True := by
  extract_vc

private theorem hidden : True := by
  extract_vc

namespace Foo

theorem bar : True := by
  extract_vc

end Foo

/-! Hypotheses become explicit arguments, before the colon. -/

theorem poly.{u} (α : Type u) (x : α) : x = x := by
  extract_vc

theorem insts {α : Type} [inst : Inhabited α] (xs : List α) : xs = xs := by
  extract_vc

example (α : Type _) (x : α) : x = x := by
  extract_vc

/-! `have`s are arguments as well, whereas `let`s stay in the statement if it depends on them. -/

theorem lets (n : Nat) : let m := n + 1; m = n + 1 := by
  intro m
  let unused := 5
  have fact : n = n := rfl
  extract_vc

/-! Names are fully qualified, since the theorem is stated outside of `open … in`. -/

open Nat in
theorem opened : succ zero = 1 := by
  extract_vc

/-! Hypotheses that cannot be referred to are named by `expose_names`. -/

theorem splitNat (n : Nat) : n = n := by
  cases n <;> extract_vc

theorem shadowed (x : Nat) (x : x = 1) : True := by
  extract_vc
