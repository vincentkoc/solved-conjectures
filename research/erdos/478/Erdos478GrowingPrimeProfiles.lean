import Erdos478RollingDeficitThreshold
import Mathlib.Analysis.SpecificLimits.Basic

/-! # One growing factorial-deficit condition preserves every prime density -/

namespace Erdos478.LowGapAction
open Finset Filter Topology MeanDeficit GapDensity GapSieve
open scoped Classical
noncomputable section

def growingPrime (p : ℕ) := rollingThreshold p≤deficit p
def cutoffError (X : ℕ) : ℝ :=
  ((Nat.primeCounting X).sqrt:ℝ)/Nat.primeCounting X+1/((observedThreshold X:ℝ)+1)

/-- The additive error is uniform over all prime events, even those depending on X. -/
theorem thinning_bounds (X : ℕ) (P : ℕ → Prop) :
    0≤fraction X P-fraction X (fun p => P p ∧ growingPrime p) ∧
    fraction X P-fraction X (fun p => P p ∧ growingPrime p)≤cutoffError X := by
  let S := Nat.primesLE X
  let T := S.filter P
  let U := S.filter fun p => P p ∧ growingPrime p
  let V := S.filter fun p => deficit p<rollingThreshold p
  let m := Nat.primeCounting X
  let q := observedThreshold X
  have count : S.card=m := Nat.primesLE_card_eq_primeCounting _
  have sub : U⊆T := fun p hp => mem_filter.mpr ⟨(mem_filter.mp hp).1,(mem_filter.mp hp).2.1⟩
  have cover : T⊆U∪V := by
    intro p hp
    obtain ⟨hs,hp⟩ := mem_filter.mp hp
    by_cases yes : growingPrime p
    · exact mem_union_left _ (mem_filter.mpr ⟨hs,hp,yes⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hs,lt_of_not_ge yes⟩)
  have le : T.card≤U.card+V.card := (card_le_card cover).trans (card_union_le ..)
  have incl : (U.card:ℝ)≤T.card := by exact_mod_cast card_le_card sub
  have bound : (T.card:ℝ)≤U.card+(m.sqrt+belowCount X q : ℕ) := by
    exact_mod_cast le.trans (Nat.add_le_add_left (rolling_exception_count X) U.card)
  have frac : fraction X P-fraction X (fun p => P p ∧ growingPrime p)=(T.card:ℝ)/m-U.card/m := by
    unfold fraction
    rw [← count]
    dsimp [T,U,S]
    congr 3
    exact congrArg Finset.card (Finset.filter_congr_decidable _ _ _)
  rw [frac]
  by_cases pos : m=0
  · simp [cutoffError,← show m=Nat.primeCounting X from rfl,pos]
    positivity
  have hm : 0<(m:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero pos)
  have hq : 0<(q:ℝ)+1 := by positivity
  have hb : (belowCount X q:ℝ)/m≤1/((q:ℝ)+1) := by
    apply (div_le_div_iff₀ hm hq).mpr
    rw [one_mul,mul_comm]
    exact_mod_cast observed_bound X
  constructor
  · exact sub_nonneg.mpr (div_le_div_of_nonneg_right incl hm.le)
  · change _≤(m.sqrt:ℝ)/m+1/((q:ℝ)+1)
    calc
      _ ≤ (m.sqrt:ℝ)/m+(belowCount X q:ℝ)/m := by
        rw [← sub_div,← add_div]
        apply div_le_div_of_nonneg_right _ hm.le
        push_cast at bound
        linarith
      _ ≤ _ := add_le_add_right hb _

theorem cutoff_error_zero (pit : DegreeOnePrimeIdealTheorem) : Tendsto cutoffError atTop (𝓝 0) := by
  let m (X : ℕ) := Nat.primeCounting X
  let s (X : ℕ) := (m X).sqrt
  have grow : Tendsto s atTop atTop := tendsto_atTop.mpr fun k =>
    (Nat.tendsto_primeCounting.eventually_ge_atTop (k^2)).mono fun _ hx => Nat.le_sqrt'.mpr hx
  have low : Tendsto (fun X => (s X:ℝ)/m X) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun X => by positivity) _ (tendsto_one_div_atTop_nhds_zero_nat.comp grow)
    filter_upwards [grow.eventually_gt_atTop 0,Nat.tendsto_primeCounting.eventually_gt_atTop 0] with X hs hm
    apply (div_le_div_iff₀ (by exact_mod_cast hm : 0<(m X:ℝ)) (by exact_mod_cast hs : 0<(s X:ℝ))).mpr
    rw [one_mul]
    exact_mod_cast Nat.sqrt_le (m X)
  have high := (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp ((tendsto_add_atTop_nat 1).comp (observed_grows pit))
  change Tendsto (fun X => (s X:ℝ)/m X+1/((observedThreshold X:ℝ)+1)) atTop (𝓝 0)
  simpa only [Function.comp_apply,Nat.cast_add,Nat.cast_one,zero_add] using low.add high

theorem growing_preserves_density (pit : DegreeOnePrimeIdealTheorem) {P : ℕ → Prop} {z : ℝ}
    (h : Tendsto (fun X => fraction X P) atTop (𝓝 z)) :
    Tendsto (fun X => fraction X (fun p => P p ∧ growingPrime p)) atTop (𝓝 z) := by
  have he := squeeze_zero (fun X => (thinning_bounds X P).1) (fun X => (thinning_bounds X P).2) (cutoff_error_zero pit)
  simpa using h.sub he

/-- A positive limiting proportion yields arbitrarily large prime witnesses. -/
theorem large_prime_of_fraction {P : ℕ → Prop} {z : ℝ} (pos : 0<z)
    (lim : Tendsto (fun X => fraction X P) atTop (𝓝 z)) (B : ℕ) : ∃ p>B, p.Prime ∧ P p := by
  by_contra! finite
  have bound (X : ℕ) : fraction X P≤((B+1:ℕ):ℝ)/Nat.primeCounting X := by
    have sub : (Nat.primesLE X).filter P⊆range (B+1) := by
      intro p hp
      obtain ⟨hx,hP⟩ := mem_filter.mp hp
      have prime := (Nat.mem_primesLE.mp hx).2
      exact mem_range.mpr (by by_contra! hg; exact finite p (by omega) prime hP)
    have le := card_le_card sub
    rw [card_range] at le
    unfold fraction
    rw [Nat.primesLE_card_eq_primeCounting]
    exact div_le_div_of_nonneg_right (by exact_mod_cast le) (Nat.cast_nonneg _)
  have zero : Tendsto (fun X : ℕ => ((B+1:ℕ):ℝ)/Nat.primeCounting X) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply] using
      (tendsto_inv_atTop_nhds_zero_nat.comp Nat.tendsto_primeCounting).const_mul ((B+1:ℕ):ℝ)
  exact pos.not_ge (le_of_tendsto_of_tendsto' lim zero bound)

#print axioms large_prime_of_fraction
#print axioms growingPrime
#print axioms cutoffError
#print axioms thinning_bounds
#print axioms cutoff_error_zero
#print axioms growing_preserves_density
end
end Erdos478.LowGapAction
