import Erdos478IdealPrimeWeights
import Erdos478DisjointGapFamilies

/-!
# Factorial deficits in power intervals

For each fixed modulus, deficit and exponent below one, every sufficiently
large cutoff contains many witness primes above the indicated power.
-/

namespace Erdos478.PowerIntervals
open Filter Topology Finset NumberField Polynomial Ideal
open Erdos478.MeanDeficit Erdos478.IdealMertens

private noncomputable def cutoff (β : ℝ) (X : ℕ) := ⌊(X:ℝ)^β⌋₊

private theorem power_top {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun X : ℕ => (X:ℝ)^β) atTop atTop :=
  (tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop

private theorem cutoff_top {β : ℝ} (hβ : 0<β) : Tendsto (cutoff β) atTop atTop :=
  tendsto_nat_floor_atTop.comp (power_top hβ)

private theorem log_cutoff {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun X : ℕ => Real.log (cutoff β X) / Real.log X) atTop (𝓝 β) := by
  have h₁ := (tendsto_nat_floor_div_atTop (R := ℝ)).comp (power_top hβ)
  have h₂ : Tendsto (fun X : ℕ => Real.log ((cutoff β X : ℝ) / (X:ℝ)^β)) atTop (𝓝 0) := by
    simpa only [Real.log_one,Function.comp_apply,cutoff] using h₁.log (by norm_num : (1:ℝ)≠0)
  have h₃ := h₂.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply (show Tendsto (fun X : ℕ => Real.log ((cutoff β X : ℝ)/(X:ℝ)^β) / Real.log X + β)
    atTop (𝓝 β) by simpa using h₃.add_const β).congr'
  filter_upwards [eventually_ge_atTop 2,(cutoff_top hβ).eventually_ge_atTop 1] with X hX hY
  have hx : (1:ℝ) < X := by exact_mod_cast (by omega : 1<X)
  have hl := Real.log_pos hx
  have hy : (0:ℝ) < cutoff β X := by exact_mod_cast hY
  rw [Real.log_div hy.ne' (Real.rpow_pos_of_pos (by linarith) β).ne',
    Real.log_rpow (by linarith : 0<(X:ℝ))]
  field_simp
  ring

private theorem window_weight (K : Type*) [Field K] [NumberField K] {β : ℝ} (hβ : 0<β) :
    Tendsto (fun X : ℕ => (degreeOneWeight K X - degreeOneWeight K (cutoff β X)) / Real.log X)
      atTop (𝓝 (1-β)) := by
  have h₁ := (degree_one_mertens K).comp (cutoff_top hβ)
  have h₂ := h₁.mul (log_cutoff hβ)
  have h₃ := (degree_one_mertens K).sub h₂
  rw [one_mul] at h₃
  apply h₃.congr'
  filter_upwards [eventually_ge_atTop 2,(cutoff_top hβ).eventually_ge_atTop 2] with X hx hy
  have hX : 0 < Real.log X := Real.log_pos (by exact_mod_cast (by omega : 1<X))
  have hY : 0 < Real.log (cutoff β X) := Real.log_pos (by exact_mod_cast (by omega : 1<cutoff β X))
  dsimp only [Function.comp_apply]
  field_simp

private theorem split_of_degree_one (f : ℤ[X]) (hf : f.Monic) (K : Type*) [Field K] [NumberField K]
    (hK : (f.map (algebraMap ℤ K)).Splits) {p : ℕ} (hp : p.Prime) (h : 0 < linearCount K p) :
    (f.map (Int.castRingHom (ZMod p))).Splits := by
  classical
  obtain ⟨P,hP⟩ := Finset.card_pos.mp h
  obtain ⟨hm,hd⟩ := mem_filter.mp hP
  have hnorm := (norm_over hp hm).1
  rw [hd,pow_one] at hnorm
  have hcard : Nat.card ((𝓞 K) ⧸ P) = p := by
    simpa only [Ideal.absNorm_apply,Submodule.cardQuot_apply] using hnorm
  let : Finite ((𝓞 K) ⧸ P) := Nat.finite_of_card_ne_zero (hcard.trans_ne hp.ne_zero)
  let : Fintype ((𝓞 K) ⧸ P) := Fintype.ofFinite _
  let φ := ((ZMod.ringEquivOfPrime _ hp (Nat.card_eq_fintype_card.symm.trans hcard)).symm.toRingHom).comp
    (Ideal.Quotient.mk P)
  have hs := (FallingGap.splits_over_integers f hf hK).map φ
  simpa only [Polynomial.map_map,RingHom.ext_int (φ.comp (algebraMap ℤ (𝓞 K))) (Int.castRingHom (ZMod p))] using hs

/-- Primes in the requested power interval satisfying a given predicate. -/
noncomputable def witnesses (W : ℕ → Prop) (α : ℝ) (X : ℕ) : Finset ℕ := by
  classical exact (Nat.primesLE X).filter fun p => (X:ℝ)^α < p ∧ W p

private theorem count_from_field (K : Type*) [Field K] [NumberField K] (W : ℕ → Prop) (B : ℕ)
    (hW : ∀ p > B, p.Prime → 0 < linearCount K p → W p)
    {α : ℝ} (hα : 0<α) (hα' : α<1) :
    ∀ᶠ X : ℕ in atTop, (X:ℝ)^α ≤ (witnesses W α X).card := by
  classical
  let β := (α+1)/2
  let c := (1-β)/2
  let d : ℝ := Module.finrank ℚ K
  have hab : α < β := by dsimp [β]; linarith
  have hb : 0 < β := hα.trans hab
  have hb1 : β < 1 := by dsimp [β]; linarith
  have hc : 0 < c := by dsimp [c]; linarith
  have hd : 0 < d := by dsimp [d]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hlim := (window_weight K hb).eventually_const_lt (show c < 1-β by dsimp [c]; linarith)
  have hscale := (power_top (sub_pos.mpr hab)).eventually_ge_atTop (d/c)
  filter_upwards [hlim,hscale,(cutoff_top hb).eventually_ge_atTop B,eventually_ge_atTop 2] with X hl hsc hB hX
  have hx : (1:ℝ) < X := by exact_mod_cast (by omega : 1<X)
  have hlog := Real.log_pos hx
  have hpwr := Real.rpow_pos_of_pos (zero_lt_one.trans hx) β
  let Y := cutoff β X
  have hy : Y ≤ X := by
    apply Nat.floor_le_of_le
    calc
      (X:ℝ)^β ≤ (X:ℝ)^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le hb1.le
      _ = _ := Real.rpow_one _
  let T := Nat.primesLE X \ Nat.primesLE Y
  let U := witnesses W α X
  let f (p : ℕ) : ℝ := (linearCount K p : ℝ) * Real.log p / p
  have hsub : Nat.primesLE Y ⊆ Nat.primesLE X := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans hy,(Nat.mem_primesLE.mp hp).2⟩
  have hm : c*Real.log X ≤ ∑ p ∈ T, f p := by
    have h := (lt_div_iff₀ hlog).mp hl
    have hsum := sum_sdiff (f := f) hsub
    change (∑ p ∈ T, f p) + degreeOneWeight K Y = degreeOneWeight K X at hsum
    change c*Real.log X < degreeOneWeight K X - degreeOneWeight K Y at h
    linarith
  let A := d*Real.log X / (X:ℝ)^β
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hub : (∑ p ∈ T, f p) ≤ (U.card : ℝ) * A := by
    calc
      _ ≤ ∑ p ∈ T, if p ∈ U then A else 0 := by
        apply sum_le_sum
        intro p hp
        obtain ⟨hin,hout⟩ := mem_sdiff.mp hp
        obtain ⟨hpX,hprime⟩ := Nat.mem_primesLE.mp hin
        have hYp : Y < p := by
          by_contra! hh
          exact hout (Nat.mem_primesLE.mpr ⟨hh,hprime⟩)
        have hreal := Nat.lt_of_floor_lt (show ⌊(X:ℝ)^β⌋₊ < p from hYp)
        by_cases hpos : 0 < linearCount K p
        · have hw := hW p (lt_of_le_of_lt hB hYp) hprime hpos
          have hup : p ∈ U := mem_filter.mpr ⟨hin,(Real.rpow_le_rpow_of_exponent_le hx.le hab.le).trans_lt hreal,hw⟩
          rw [if_pos hup]
          apply div_le_div₀ _ _ hpwr hreal.le
          · exact mul_nonneg hd.le hlog.le
          · apply mul_le_mul _ (Real.log_le_log (by exact_mod_cast hprime.pos) (by exact_mod_cast hpX))
              (Real.log_nonneg (by exact_mod_cast hprime.one_le)) hd.le
            dsimp [d]
            exact_mod_cast linearCount_le (K := K) hprime
        · have hz : linearCount K p = 0 := Nat.eq_zero_of_not_pos hpos
          simp only [f,hz,Nat.cast_zero,zero_mul,zero_div]
          split_ifs <;> positivity
      _ = ((T.filter (· ∈ U)).card : ℝ) * A := by rw [← sum_filter,sum_const,nsmul_eq_mul]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hA
        exact_mod_cast card_le_card (show T.filter (· ∈ U) ⊆ U from fun _ h => (mem_filter.mp h).2)
  have hmass := hm.trans hub
  change c*Real.log X ≤ (U.card : ℝ) * (d*Real.log X/(X:ℝ)^β) at hmass
  rw [← mul_div_assoc,le_div_iff₀ hpwr] at hmass
  have hcard : c*(X:ℝ)^β ≤ (U.card:ℝ)*d := by
    apply (le_of_mul_le_mul_right · hlog)
    linarith only [hmass]
  have hsc' := (div_le_iff₀ hc).mp hsc
  have he : (X:ℝ)^β = (X:ℝ)^α * (X:ℝ)^(β-α) := by
    rw [← Real.rpow_add (by linarith),add_sub_cancel]
  rw [he] at hcard
  apply (le_of_mul_le_mul_right · hd)
  have hmul := mul_le_mul_of_nonneg_left hsc' (Real.rpow_nonneg (Nat.cast_nonneg X) α)
  linarith only [hcard,hmul]

/-- Every sufficiently large power interval contains many completely splitting primes
of a given monic integral polynomial, with any fixed finite exception removed. -/
theorem splitting_primes_in_power_intervals (t : ℤ[X]) (ht : t.Monic) (W : ℕ → Prop) (B : ℕ)
    (hW : ∀ p > B, p.Prime → (t.map (Int.castRingHom (ZMod p))).Splits → W p)
    {α : ℝ} (hα : 0<α) (hα' : α<1) :
    ∀ᶠ X : ℕ in atTop, (X:ℝ)^α ≤ (witnesses W α X).card := by
  let F := t.map (algebraMap ℤ ℚ)
  let K := F.SplittingField
  let : NumberField K := {}
  have hsplit : (t.map (algebraMap ℤ K)).Splits := by
    simpa only [F,Polynomial.map_map,← IsScalarTower.algebraMap_eq] using SplittingField.splits F
  exact count_from_field K W B (fun p hp hpr h => hW p hp hpr (split_of_degree_one t ht K hsplit hpr h)) hα hα'

/-- At all sufficiently large cutoffs X the interval (X^α,X] contains at least X^α
primes congruent to one modulo m and missing at least D factorial residues. -/
theorem eventual_many_deficit_primes (D m : ℕ) (hm : 0<m) {α : ℝ} (hα : 0<α) (hα' : α<1) :
    ∀ᶠ X : ℕ in atTop, (X:ℝ)^α ≤ (witnesses (fun p =>
      m ∣ p-1 ∧ ((Ico 1 p).image (fun n => n.factorial % p)).card + D ≤ p) α X).card := by
  obtain ⟨t,ht,_,B,hB⟩ := GapFamilies.progression_splitting_test D m hm
  apply splitting_primes_in_power_intervals t ht _ B _ hα hα'
  intro p hp hpr hsplit
  obtain ⟨hm',_,_,hd⟩ := hB p hp hpr hsplit
  refine ⟨hm',?_⟩
  have hD : D ≤ (D+2).choose 2 := by
    rw [Nat.choose_two_right,Nat.le_div_iff_mul_le (by decide : 0 < 2)]
    rw [show D+2-1 = D+1 by omega]
    nlinarith only [Nat.zero_le (D*D)]
  omega

#print axioms splitting_primes_in_power_intervals
#print axioms eventual_many_deficit_primes

end Erdos478.PowerIntervals
