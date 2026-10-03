module

/-!
What `extract_goal` suggests: the theorem it extracts from the main goal, and the tactic that closes
the goal with it.
-/

/-!
The theorem is named after the enclosing declaration and the goal's case tag, unless `using` names
it.
-/

theorem womp : True := by
  extract_goal

example : True := by
  extract_goal

private theorem hidden : True := by
  extract_goal

namespace Foo

theorem bar : True := by
  extract_goal

theorem named : True := by
  extract_goal using baz

end Foo

/-! Hypotheses become explicit arguments, before the colon. -/

theorem poly.{u} (α : Type u) (x : α) : x = x := by
  extract_goal

theorem insts {α : Type} [inst : Inhabited α] (xs : List α) : xs.headD default ∈ xs ∨ xs = [] := by
  extract_goal

example (α : Type _) (x : α) : x = x := by
  extract_goal

/-!
Only the hypotheses that are relevant to the goal are kept: those it mentions, what they depend on,
and propositions about them. For `False`, all are kept. `*` keeps all of them, and named hypotheses
are kept along with what they depend on.
-/

theorem relevant (n m k : Nat) (hn : n = 1) (hm : m = 2) : n = 1 := by
  extract_goal

theorem contradiction (n m : Nat) (h : n < 0) : False := by
  extract_goal

theorem all (n m : Nat) (hn : n = 1) (hm : m = 2) : n = 1 := by
  extract_goal *

theorem chosen (n m k : Nat) (hn : n = 1) (hm : m = 2) : n = n := by
  extract_goal hm

/-! `have`s are arguments as well, whereas `let`s stay in the statement if it depends on them. -/

theorem lets (n : Nat) : let m := n + 1; m = n + 1 := by
  intro m
  let unused := 5
  have fact : n = n := rfl
  extract_goal

/-! Names are fully qualified, since the theorem is stated outside of `open … in`. -/

open Nat in
theorem opened : succ zero = 1 := by
  extract_goal

/-! Hypotheses that cannot be referred to are named by `expose_names`. -/

theorem splitNat (n : Nat) : n = n := by
  cases n <;> extract_goal

theorem shadowed (x : Nat) (x : x = 1) : True := by
  extract_goal *

/-! A goal that is not a proposition becomes a definition. -/

def data (n : Nat) : Fin (n + 1) := by
  extract_goal

/-!
Scoped notation and scoped instances that the statement relies on stay available through
`open scoped`, since the theorem is stated outside of `open … in`.
-/

namespace Scoped
public def double (n : Nat) := n + n
scoped notation "⟪" n "⟫" => double n
end Scoped

open Scoped in
theorem usesScoped (n : Nat) : ⟪n⟫ = n + n := by
  extract_goal

/-! Notation that is local to the file stays usable, since the theorem is stated in the file. -/

section
local notation "dbl! " n:max => Scoped.double n

theorem usesLocal (n : Nat) : dbl! n = n + n := by
  extract_goal
end
