import Mathlib.NumberTheory.Wilson
import Mathlib.Tactic

/-! A finite upper bound for the factorial-residue set of Erdős problem 478
when 5 is a quadratic residue. -/

namespace Erdos478

open Finset

/-- Each index with an earlier witness of the same value can be discarded simultaneously. -/
private theorem card_image_le_discard (s t : Finset ℕ) (f : ℕ → ℕ) (ht : t ⊆ s)
    (hw : ∀ i ∈ t, ∃ j ∈ s, j < i ∧ f j = f i) :
    (s.image f).card ≤ s.card - t.card := by
  classical
  have hsub : s.image f ⊆ (s \ t).image f := by
    intro y hy
    obtain ⟨i, hi, hiy⟩ := Finset.mem_image.mp hy
    have h : ∃ j, j ∈ s ∧ f j = y := ⟨i, hi, hiy⟩
    obtain ⟨hs, he⟩ := Nat.find_spec h
    refine Finset.mem_image.mpr ⟨Nat.find h, Finset.mem_sdiff.mpr ⟨hs, ?_⟩, he⟩
    intro ht'
    obtain ⟨j, hj, hlt, hfj⟩ := hw _ ht'
    exact Nat.find_min h hlt ⟨hj, hfj.trans he⟩
  exact (Finset.card_le_card hsub).trans
    (Finset.card_image_le.trans_eq (Finset.card_sdiff_of_subset ht))

/-- A root of `x(x-1)=1` gives equal factorials at the indices `x.val-2` and `x.val`. -/
private theorem gap_two {p : ℕ} [Fact p.Prime] (hp : 5 < p)
    (x : ZMod p) (hx : x * (x - 1) = 1) :
    3 ≤ x.val ∧ x.val ≠ p - 2 ∧
      (x.val - 2).factorial % p = x.val.factorial % p := by
  have h5 : (5 : ZMod p) ≠ 0 := fun h =>
    Nat.not_dvd_of_pos_of_lt (by decide) hp ((ZMod.natCast_eq_zero_iff 5 p).mp h)
  have hlo : 3 ≤ x.val := by
    by_contra! h
    have hcases : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by omega
    rcases hcases with h | h | h <;> rw [← ZMod.natCast_zmod_val x, h] at hx <;> norm_num at hx
    exact one_ne_zero (by linear_combination hx : (1 : ZMod p) = 0)
  have hne : x.val ≠ p - 2 := by
    intro he
    have he' : x = -2 := by
      rw [← ZMod.natCast_zmod_val x, he, Nat.cast_sub (by omega : 2 ≤ p)]
      simp
    rw [he'] at hx
    exact h5 (by linear_combination hx)
  refine ⟨hlo, hne, (ZMod.natCast_eq_natCast_iff' _ _ _).mp ?_⟩
  let n := x.val - 2
  have hn : x.val = n + 2 := by dsimp [n]; omega
  have hx' : (n : ZMod p) + 2 = x := by
    simpa using (show ((n + 2 : ℕ) : ZMod p) = x by rw [← hn, ZMod.natCast_zmod_val])
  change (n.factorial : ZMod p) = (x.val.factorial : ZMod p)
  rw [hn, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  have hprod : ((n : ZMod p) + 2) * ((n : ZMod p) + 1) = 1 := by
    rw [← hx'] at hx
    linear_combination hx
  linear_combination -(n.factorial : ZMod p) * hprod

/-- If 5 is a square modulo a prime greater than 5, at least three indices in
`[1,p)` repeat earlier factorial residues. -/
theorem card_factorial_residues_le_sub_four {p : ℕ} (hprime : p.Prime) (hp : 5 < p)
    (hsq : IsSquare (5 : ZMod p)) :
    ((Finset.Ico 1 p).image (fun k => Nat.factorial k % p)).card ≤ p - 4 := by
  let : Fact p.Prime := ⟨hprime⟩
  have hsmall (n : ℕ) (hn : 0 < n) (hl : n < p) : (n : ZMod p) ≠ 0 := fun h =>
    Nat.not_dvd_of_pos_of_lt hn hl ((ZMod.natCast_eq_zero_iff n p).mp h)
  have h2 : (2 : ZMod p) ≠ 0 := hsmall 2 (by decide) (by omega)
  obtain ⟨r, hr⟩ := hsq
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, mul_zero] at hr
    exact hsmall 5 (by decide) hp hr
  let x : ZMod p := (1 + r) / 2
  let y : ZMod p := (1 - r) / 2
  have hx : x * (x - 1) = 1 := by
    dsimp [x]; field_simp; linear_combination -hr
  have hy : y * (y - 1) = 1 := by
    dsimp [y]; field_simp; linear_combination -hr
  have hxy : x.val ≠ y.val := by
    intro e
    have h := ZMod.val_injective p e
    change (1 + r) / 2 = (1 - r) / 2 at h
    field_simp at h
    exact hr0 ((mul_eq_zero.mp (show (2 : ZMod p) * r = 0 by linear_combination h)).resolve_left h2)
  obtain ⟨hxlo, hxp, hxf⟩ := gap_two hp x hx
  obtain ⟨hylo, hyp, hyf⟩ := gap_two hp y hy
  have hW : 1 % p = (p - 2).factorial % p := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
    have hw := ZMod.wilsons_lemma p
    rw [show p - 1 = (p - 2) + 1 by omega, Nat.factorial_succ, Nat.cast_mul] at hw
    have hneg : (((p - 2 + 1 : ℕ)) : ZMod p) = -1 := by
      rw [Nat.cast_add, Nat.cast_sub (by omega : 2 ≤ p)]
      simp only [ZMod.natCast_self, Nat.cast_ofNat, Nat.cast_one, zero_sub]
      ring
    rw [hneg] at hw
    simpa using hw.symm
  let t : Finset ℕ := {x.val, y.val, p - 2}
  have hxt := x.val_lt
  have hyt := y.val_lt
  have ht (i : ℕ) : i ∈ t ↔ i = x.val ∨ i = y.val ∨ i = p - 2 := by simp [t]
  have hbound := card_image_le_discard (Ico 1 p) t (fun k => k.factorial % p)
    (by intro i hi; rcases (ht i).mp hi with rfl | rfl | rfl <;> simp only [mem_Ico] <;> omega)
    (by
      intro i hi
      rcases (ht i).mp hi with rfl | rfl | rfl
      · exact ⟨_, mem_Ico.mpr ⟨by omega, by omega⟩, by omega, hxf⟩
      · exact ⟨_, mem_Ico.mpr ⟨by omega, by omega⟩, by omega, hyf⟩
      · exact ⟨1, mem_Ico.mpr ⟨le_rfl, by omega⟩, by omega, by simpa using hW⟩)
  have hcard : t.card = 3 := by simp [t, hxy, hxp, hyp]
  rw [hcard, Nat.card_Ico] at hbound
  exact hbound

#print axioms card_factorial_residues_le_sub_four

end Erdos478
