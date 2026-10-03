import Std.Tactic.Do
import Std

/-!
Goals that `extract_vc` and `extract_vcs` cannot state as a theorem: those with metavariables or
`sorry`, and those that are not propositions, such as the goal `mvcgen` leaves for an invariant that
has not been supplied. `extract_vcs` extracts either every goal or none.
-/

example : True := by
  have h : (?n : Nat) = ?n := rfl
  extract_vc

example : (sorry : Nat) = 0 := by
  extract_vc

def data : Nat := by
  extract_vc

example : True ∧ True := by
  constructor
  have h : (?n : Nat) = ?n := rfl
  extract_vcs

example : True := by
  trivial
  extract_vcs

def mySum (l : List Nat) : Nat := Id.run do
  let mut acc := 0
  for x in l do
    acc := acc + x
  return acc

open Std Do in
set_option linter.deprecated.syntax false in
theorem noInvariant (l : List Nat) : mySum l = l.sum := by
  generalize h : mySum l = r
  apply Id.of_wp_run_eq h
  mvcgen
  extract_vcs
