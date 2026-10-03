import Std.WP

/-!
Goals that `extract_goal` and `extract_goals` cannot state as a theorem: those with metavariables,
such as the goals that `vcgen` leaves when an invariant has not been supplied, and those with
`sorry`. `extract_goals` extracts either every goal or none. A name given with `using` must be free
or name a theorem that states the goal. A statement that uses notation local to this file cannot be
put into the file of another module.
-/

example : True := by
  have h : (?n : Nat) = ?n := rfl
  extract_goal *

example : (sorry : Nat) = 0 := by
  extract_goal

example : True ∧ True := by
  constructor
  have h : (?n : Nat) = ?n := rfl
  extract_goals *

example : True := by
  trivial
  extract_goals

theorem taken : True := trivial

example : 1 = 1 := by
  extract_goal using taken

def twice (n : Nat) := n + n

local notation "dbl! " n:max => twice n

example (n : Nat) : dbl! n = n + n := by
  extract_goal into Example.VCs

def mySum (l : List Nat) : Nat := Id.run do
  let mut acc := 0
  for x in l do acc := acc + x
  return acc

open Std.WP in
set_option experimental.vcgen true in
theorem noInvariant (l : List Nat) : mySum l = l.sum := by
  generalize h : mySum l = r
  apply Id.of_run_eq_wp h
  vcgen [mySum]
  extract_goals
