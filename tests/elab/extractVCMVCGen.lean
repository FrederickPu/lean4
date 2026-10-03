import Std.Tactic.Do
import Std

/-!
`extract_vcs` after `mvcgen`: it extracts the verification conditions that `mvcgen` leaves behind.
The suggestion, applied and with the extracted theorem proved, completes the proof.
-/

open Std Do

set_option grind.warning false
set_option linter.deprecated.syntax false

def mySum (l : List Nat) : Nat := Id.run do
  let mut acc := 0
  for x in l do
    acc := acc + x
  return acc

theorem mySum_correct (l : List Nat) : mySum l = l.sum := by
  generalize h : mySum l = r
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, acc⟩ => ⌜acc = xs.prefix.sum⌝
  extract_vcs

/-! The suggestion above, applied, with the extracted theorem proved. -/

theorem mySum_correct'.vc1.step (l : List Nat) (r : Nat) (h : mySum l = r) (pref : List Nat) (cur : Nat)
    (suff : List Nat) (h_1 : l = pref ++ cur :: suff) (b : Nat) (h_2 : b = pref.sum) :
    b + cur = (pref ++ [cur]).sum := by
  simp_all [Nat.add_comm]

theorem mySum_correct' (l : List Nat) : mySum l = l.sum := by
  generalize h : mySum l = r
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, acc⟩ => ⌜acc = xs.prefix.sum⌝
  expose_names; exact mySum_correct'.vc1.step l r h pref cur suff h_1 b h_2
