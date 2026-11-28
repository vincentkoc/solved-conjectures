import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Stationarity error for a contractive chain started from a deterministic seed. -/

namespace Green54LangevinConvergence
open MeasureTheory
open scoped NNReal
variable {V : Type*} [PseudoMetricSpace V]
theorem iterate_lip (P : (V → ℝ) → V → ℝ) {r : NNReal}
    (hc : ∀ {K : NNReal} {f : V → ℝ}, LipschitzWith K f → LipschitzWith (r*K) (P f))
    {K : NNReal} {f : V → ℝ} (hf : LipschitzWith K f) (n : ℕ) :
    LipschitzWith (r^n*K) (P^[n] f) := by
  induction n with
  | zero => simpa using hf
  | succ n ih => simpa only [pow_succ', mul_assoc, Function.iterate_succ_apply'] using hc ih

theorem telescoping_bias (P : (V → ℝ) → V → ℝ) (Λ : (V → ℝ) → ℝ) {r : NNReal} {δ : ℝ}
    (hc : ∀ {K : NNReal} {f : V → ℝ}, LipschitzWith K f → LipschitzWith (r*K) (P f))
    (herr : ∀ {K : NNReal} {f : V → ℝ}, LipschitzWith K f → |Λ (P f)-Λ f| ≤ δ*(K:ℝ))
    {K : NNReal} {f : V → ℝ} (hf : LipschitzWith K f) (n : ℕ) :
    |Λ (P^[n] f)-Λ f| ≤ δ*(K:ℝ)*∑ j ∈ Finset.range n, (r:ℝ)^j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := herr (iterate_lip P hc hf n)
    simp only [Function.iterate_succ_apply', Finset.sum_range_succ]
    have ht := abs_sub_le (Λ (P (P^[n] f))) (Λ (P^[n] f)) (Λ f)
    push_cast at h
    nlinarith

variable [MeasurableSpace V] [BorelSpace V]
private theorem integrable_lip (π : Measure V) [IsProbabilityMeasure π] (x₀ : V)
    (h₀ : Integrable (dist x₀) π) {K : NNReal} {f : V → ℝ} (hf : LipschitzWith K f) :
    Integrable f π := by
  apply ((h₀.const_mul K).add (integrable_const ‖f x₀‖)).mono' hf.continuous.aestronglyMeasurable
  apply ae_of_all
  intro y
  have hd := hf.dist_le_mul y x₀
  rw [dist_comm y x₀, dist_eq_norm] at hd
  change ‖f y‖ ≤ (K:ℝ)*dist x₀ y + ‖f x₀‖
  linarith [norm_sub_norm_le (f y) (f x₀)]

private theorem seed_mean_distance (π : Measure V) [IsProbabilityMeasure π] (x₀ : V)
    (h₀ : Integrable (dist x₀) π) {K : NNReal} {f : V → ℝ} (hf : LipschitzWith K f) :
    |f x₀ - ∫ y, f y ∂π| ≤ K * ∫ y, dist x₀ y ∂π := by
  calc
    _ = ‖∫ y, f x₀ - f y ∂π‖ := by
      rw [integral_sub (integrable_const _) (integrable_lip π x₀ h₀ hf)]
      simp
    _ ≤ ∫ y, (K : ℝ)*dist x₀ y ∂π := norm_integral_le_of_norm_le (h₀.const_mul K)
      (ae_of_all _ fun y => by simpa only [dist_eq_norm] using hf.dist_le_mul x₀ y)
    _ = _ := integral_const_mul _ _

/-- A contractive transition propagates a one-step stationarity error geometrically.
The seed may be deterministic and the test function may be unbounded. -/
theorem endpoint_bias (π : Measure V) [IsProbabilityMeasure π] (x₀ : V)
    (h₀ : Integrable (dist x₀) π) (P : (V → ℝ) → V → ℝ) {r : NNReal} (hr : (r:ℝ) < 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hc : ∀ {K : NNReal} {f : V → ℝ}, LipschitzWith K f → LipschitzWith (r*K) (P f))
    (herr : ∀ {K : NNReal} {f : V → ℝ}, LipschitzWith K f →
      |(∫ x, P f x-f x ∂π)| ≤ δ*(K:ℝ))
    {K : NNReal} {f : V → ℝ} (hf : LipschitzWith K f) (n : ℕ) :
    |P^[n] f x₀ - ∫ y, f y ∂π| ≤
      (K:ℝ) * ((r:ℝ)^n * (∫ y, dist x₀ y ∂π) + δ / (1-r)) := by
  have ha := seed_mean_distance π x₀ h₀ (iterate_lip P hc hf n)
  have he {k : NNReal} {g : V → ℝ} (hg : LipschitzWith k g) :
      |(∫ x, P g x ∂π)-(∫ x, g x ∂π)| ≤ δ*(k:ℝ) := by
    rw [← integral_sub (integrable_lip π x₀ h₀ (hc hg)) (integrable_lip π x₀ h₀ hg)]
    exact herr hg
  have hb := telescoping_bias P (fun g => ∫ y, g y ∂π) hc he hf n
  have ht := abs_sub_le (P^[n] f x₀) (∫ y, P^[n] f y ∂π) (∫ y, f y ∂π)
  have hsum : (∑ j ∈ Finset.range n, (r:ℝ)^j) ≤ 1/(1-(r:ℝ)) := by
    apply (le_div_iff₀ (sub_pos.mpr hr)).mpr
    rw [geom_sum_mul_neg]
    linarith [pow_nonneg r.coe_nonneg n]
  push_cast at ha
  have hc' := mul_le_mul_of_nonneg_left hsum (mul_nonneg hδ K.coe_nonneg)
  linarith only [ht,ha,hb,hc', show δ*(K:ℝ)*(1/(1-(r:ℝ)))=(K:ℝ)*(δ/(1-r)) by ring,
    show ((r:ℝ)^n*(K:ℝ))*(∫ y, dist x₀ y ∂π) + (K:ℝ)*(δ/(1-r)) =
      (K:ℝ)*((r:ℝ)^n*(∫ y, dist x₀ y ∂π) + δ/(1-r)) by ring]

#print axioms endpoint_bias
#print axioms telescoping_bias
end Green54LangevinConvergence
