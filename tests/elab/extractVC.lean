module

/-!
`extract_vc` names the extracted theorem, renames inaccessible hypotheses, lists universe
parameters, and replaces the tactic with `exact <theorem>`.
-/

/-- exact womp.goal -/
#guard_msgs (info, drop warning, whitespace := lax, substring := true) in
theorem womp : True := by
  extract_vc

/-- exact extracted.goal -/
#guard_msgs (info, drop warning, whitespace := lax, substring := true) in
example : True := by
  extract_vc

/-- private theorem hidden.goal -/
#guard_msgs (info, drop warning, whitespace := lax, substring := true) in
private theorem hidden : True := by
  extract_vc

/-- exact poly.goal α x -/
#guard_msgs (info, drop warning, whitespace := lax, substring := true) in
theorem poly.{u} (α : Type u) (x : α) : x = x := by
  extract_vc

/-- rename_i n_1; exact splitNat.succ n_1 -/
#guard_msgs (info, drop warning, whitespace := lax, substring := true) in
theorem splitNat (n : Nat) : n = n := by
  cases n <;> extract_vc

namespace Foo

/-- exact bar.goal -/
#guard_msgs (info, drop warning, whitespace := lax, substring := true) in
theorem bar : True := by
  extract_vc

end Foo

/-- exact opened.goal -/
#guard_msgs (info, drop warning, whitespace := lax, substring := true) in
open Nat in
theorem opened : Nat.zero = 0 := by
  extract_vc

/--
error: extract_vc: goal contains metavariables; supply invariants first
-/
#guard_msgs (error, substring := true) in
example : True := by
  have : ?a := by
    extract_vc
  trivial
