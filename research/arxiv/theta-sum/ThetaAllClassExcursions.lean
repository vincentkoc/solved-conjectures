import ThetaCompatibleCounts
import ThetaLargeLawTails

/-! Lower fractions of all primes in both extreme tails in every reduced progression. -/
namespace Arxiv.«2501.03234».ThetaAllClassExcursions
open Finset Filter Real ThetaNaturalPrimeMeans ThetaCharacterPrimeMeans ThetaPrimeDensity
open ThetaDiagonalConstant ThetaFactorialSequence
open scoped Topology
noncomputable section

/-- For each fixed reduced class the same explicit fraction holds at all
sufficiently large heights. Both thresholds for eventuality may depend on the class. -/
theorem counts (hAP : ProgressionMangoldt) {q r : ℕ} (hq : 0 < q)
    (hr : r < q) (hc : r.Coprime q) :
    ∀ᶠ b : ℝ in atTop, ∀ᶠ X : ℕ in atTop,
      let d := exp (-(exp (32*Real.pi*sqrt b)))*X.primeCounting
      d ≤ ((primeSet (fun p => p%q=r ∧ diagonalConstant+b<(S p:ℝ)/p-log p/2) X).card:ℝ) ∧
      d ≤ ((primeSet (fun p => p%q=r ∧ (S p:ℝ)/p-log p/2<diagonalConstant-b) X).card:ℝ) := by
  classical
  obtain ⟨C,hC,H⟩ := ThetaCompatibleCounts.sequence_counts hAP
  filter_upwards [ThetaLargeLawTails.height_scale hC _ (H q r hq hr hc)] with b hb
  obtain ⟨T,hX,ht,he⟩ := hb
  filter_upwards [hX] with X h
  have hd := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg X.primeCounting)
  rw [one_div,inv_mul_eq_div] at hd
  constructor
  · apply hd.trans (h.1.trans _)
    apply Nat.cast_le.mpr; apply card_le_card; intro p hp
    simp only [primeSet,mem_filter] at hp ⊢
    exact ⟨hp.1,hp.2.1,(add_lt_add_right ht _).trans hp.2.2⟩
  · apply hd.trans (h.2.trans _)
    apply Nat.cast_le.mpr; apply card_le_card; intro p hp
    simp only [primeSet,mem_filter] at hp ⊢
    exact ⟨hp.1,hp.2.1,hp.2.2.trans (sub_lt_sub_left ht _)⟩

/-- Every prescribed height has a positive lower fraction of all primes on
both sides inside the prescribed class. -/
theorem every_height (hAP : ProgressionMangoldt) {q r : ℕ} (hq : 0 < q)
    (hr : r < q) (hc : r.Coprime q) (b : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ X : ℕ in atTop,
      δ*X.primeCounting ≤ ((primeSet (fun p => p%q=r ∧ diagonalConstant+b<(S p:ℝ)/p-log p/2) X).card:ℝ) ∧
      δ*X.primeCounting ≤ ((primeSet (fun p => p%q=r ∧ (S p:ℝ)/p-log p/2<diagonalConstant-b) X).card:ℝ) := by
  classical
  obtain ⟨t,H,ht⟩ := ((counts hAP hq hr hc).and (eventually_ge_atTop b)).exists
  refine ⟨exp (-(exp (32*Real.pi*sqrt t))),exp_pos _,?_⟩
  filter_upwards [H] with X h
  constructor
  · apply h.1.trans; apply Nat.cast_le.mpr; apply card_le_card; intro p hp
    simp only [primeSet,mem_filter] at hp ⊢
    exact ⟨hp.1,hp.2.1,(add_le_add_right ht _).trans_lt hp.2.2⟩
  · apply h.2.trans; apply Nat.cast_le.mpr; apply card_le_card; intro p hp
    simp only [primeSet,mem_filter] at hp ⊢
    exact ⟨hp.1,hp.2.1,hp.2.2.trans_le (sub_le_sub_left ht _)⟩

#print axioms counts
#print axioms every_height
end
end Arxiv.«2501.03234».ThetaAllClassExcursions
