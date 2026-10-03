import Std.WP

/-!
`extract_goals` after `vcgen`: it extracts the verification conditions that `vcgen` leaves behind.
The suggestion, applied and with the extracted theorems proved, completes the proof.
-/

open Std.WP Lean.Order

set_option experimental.vcgen true

def mySum (l : List Nat) : Nat := Id.run do
  let mut acc := 0
  for x in l do acc := acc + x
  return acc

theorem mySum_correct (l : List Nat) : mySum l = l.sum := by
  generalize h : mySum l = r
  apply Id.of_run_eq_wp h
  vcgen [mySum] invariants
  · fun _pref suff acc => ⌜acc + suff.sum = l.sum⌝
  extract_goals

/-! The suggestion above, applied, with the extracted theorems proved. -/

theorem mySum_correct'.vc1 (l : List Nat) (r : Nat) (h : mySum l = r) : 0 + l.sum = l.sum := by
  simp

theorem mySum_correct'.vc2 (l : List Nat) (r : Nat) (h : mySum l = r) (a : Nat)
    (h_1 : a + [].sum = l.sum) : a = l.sum := by
  simpa using h_1

theorem mySum_correct'.vc3 (l : List Nat) (r : Nat) (h : mySum l = r) (pref : List Nat) (cur : Nat)
    (suff : List Nat) (_h : l = pref ++ cur :: suff) (b : Nat) (h_1 : b + (cur :: suff).sum = l.sum) :
    let acc : Nat := b + cur;
    ⌜acc + suff.sum = l.sum⌝ := by
  intro acc
  rw [CompleteLattice.ofProp_prop_eq]
  simp only [List.sum_cons] at h_1
  simp only [acc]
  omega

theorem mySum_correct' (l : List Nat) : mySum l = l.sum := by
  generalize h : mySum l = r
  apply Id.of_run_eq_wp h
  vcgen [mySum] invariants
  · fun _pref suff acc => ⌜acc + suff.sum = l.sum⌝
  exact mySum_correct'.vc1 l r h
  expose_names; exact mySum_correct'.vc2 l r h a h_1
  expose_names; exact mySum_correct'.vc3 l r h pref cur suff _h b h_1

/-!
In the file of another module, the theorems open what their statements rely on: `⌜⌝` is notation
scoped to `Lean.Order`, and the lattice structure of `Prop` is a scoped instance.
-/

theorem mySum_correct_into (l : List Nat) : mySum l = l.sum := by
  generalize h : mySum l = r
  apply Id.of_run_eq_wp h
  vcgen [mySum] invariants
  · fun _pref suff acc => ⌜acc + suff.sum = l.sum⌝
  extract_goals into Example.VCs
