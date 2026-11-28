import Erdos722AllResidueIntervals
import Erdos722ResidueDilation
import Erdos722CoprimeScales
import Erdos722HananiFour

/-!
# Wilson's eventual spectrum for Steiner pair designs

Two coprime interval dilations cover a tail of every admissible group
count. The final equivalence uses the binomial divisibility tests of
the pinned rank-two statement of Erdős 722.
-/

namespace Erdos722.PairDesign
open Erdos722.Quartet Filter

private theorem iterate_residues {P : ℕ → Prop} {k J c : ℕ}
    (step : ∀ {l h}, FullFor P k J l h → FullFor P k J (c*l) (c*h))
    {l h : ℕ} (H : FullFor P k J l h) (e : ℕ) : FullFor P k J (c^e*l) (c^e*h) := by
  induction e with
  | zero => simpa using H
  | succ e ih => simpa only [pow_succ',Nat.mul_assoc] using step ih

theorem all_group_counts {k : ℕ} (hk : 2≤k) : ∃ N, ∀ u≥N, Allowed k u → Local k u := by
  obtain ⟨s,hs,hks,_,S⟩ := adjacent_multiples hk 1 1 (by decide)
  let c := s+1
  obtain ⟨t,ht,hkt,hct,T⟩ := adjacent_multiples hk c 1 (by dsimp [c]; omega)
  let d := t+1
  have hc : 1<c := by dsimp [c]; omega
  have hd : 1<d := by dsimp [d]; omega
  obtain ⟨a,ha⟩ := hct
  have hcop : c.Coprime d := by
    dsimp [d]
    rw [ha,Nat.mul_comm,Nat.add_comm,Nat.coprime_add_mul_right_right]
    simp
  obtain ⟨N,hN⟩ := eventual_arrays (by omega : 2≤c)
  obtain ⟨M,hM⟩ := eventual_arrays (by omega : 2≤d)
  let J := N+M+(c+d)*(k+2)
  have hcj : c*(k+2)≤J := by dsimp [J]; nlinarith only [Nat.zero_le (d*(k+2)),Nat.zero_le N,Nat.zero_le M]
  have hdj : d*(k+2)≤J := by dsimp [J]; nlinarith only [Nat.zero_le (c*(k+2)),Nat.zero_le N,Nat.zero_le M]
  have hJ : 0<J := lt_of_lt_of_le (by positivity) hcj
  obtain ⟨L,hL,h⟩ := all_seed_interval hk hs hks S (12*J+2)
  let l := L+4*J
  have initial : FullFor (Allowed k) k J l (l+1) := by
    refine ⟨by dsimp [l]; omega,?_⟩
    intro u hlo hhi hu
    exact h u (by dsimp [l] at hlo; omega) (by dsimp [l] at hhi; omega)
      ((allowed_congr (Nat.mod_modEq u k)).mp hu)
  have zero : Allowed k 0 := by simp [Allowed]
  obtain ⟨B,hB⟩ := Scales.scale_cover hc hd hcop (by dsimp [l]; omega : 0<l) (Nat.lt_succ_self l)
  refine ⟨B,?_⟩
  intro u hu ha
  obtain ⟨_,⟨i,j,rfl⟩,hlo,hhi⟩ := hB u hu
  have D := iterate_residues (c:=d) (dilate_for zero hk ht hkt T hM (by dsimp [J]; omega) hdj) initial j
  have C := iterate_residues (c:=c) (dilate_for zero hk hs hks S hN (by dsimp [J]; omega) hcj) D i
  have H : FullFor (Allowed k) k J (l*(c^i*d^j)) ((l+1)*(c^i*d^j)) := by
    simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using C
  exact H.2 u (hlo.trans (Nat.le_add_right ..)) (hhi.trans (Nat.le_add_right ..))
    ((allowed_congr (Nat.mod_modEq u k)).mpr ha)

/-- Wilson's exact eventual spectrum for Steiner pair designs, with the two
binomial divisibility conditions used in Erdős 722. -/
theorem pair_design_spectrum (k : ℕ) (hk : 2≤k) :
    ∀ᶠ n : ℕ in atTop, (∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 2 k) ↔
      ∀ i<2, (k-i).choose (2-i) ∣ (n-i).choose (2-i) := by
  obtain ⟨N,hN⟩ := all_group_counts hk
  filter_upwards [eventually_ge_atTop ((k-1)*N+1)] with n hn
  constructor
  · rintro ⟨H,hH⟩ i hi
    exact design_divisibility hH (by omega) (by omega)
  · intro h
    have h₁ : k-1 ∣ n-1 := by simpa using h 1 (by decide)
    have h₂ : k.choose 2 ∣ n.choose 2 := by simpa using h 0 (by decide)
    obtain ⟨u,hu⟩ := h₁
    have he : (k-1)*u+1=n := by omega
    have hle : N≤u := Nat.le_of_mul_le_mul_left (by omega : (k-1)*N≤(k-1)*u) (by omega)
    have ha := (allowed_iff_pairs (u:=u) hk).mpr (he ▸ h₂)
    exact he ▸ (hN u hle ha).some.design

/-- Rank two, with the quantifier order in the pinned conjecture. -/
theorem eventually_pair_design (k : ℕ) (hk : 2<k) :
    ∀ᶠ n : ℕ in atTop, (∀ i<2, (k-i).choose (2-i) ∣ (n-i).choose (2-i)) →
      ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 2 k :=
  (pair_design_spectrum k hk.le).mono fun _ h => h.mpr

#print axioms all_group_counts
#print axioms pair_design_spectrum
#print axioms eventually_pair_design
end Erdos722.PairDesign
