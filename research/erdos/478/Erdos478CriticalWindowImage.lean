import Erdos478WindowScales

/-! # Positive mean image density at every fixed multiple of the square-root scale -/

namespace Erdos478.WindowAverage
open Finset Filter Topology
noncomputable section

def imageError (p H : ℕ) : ℝ := (H:ℝ)*(H+2)/(6*(starts p H).card)

private theorem error_limit (H : ℕ → ℕ) (L : ℝ)
    (low : Tendsto (fun p => (H p:ℝ)/p) alongPrimes (𝓝 0))
    (sq : Tendsto (fun p => (H p:ℝ)^2/p) alongPrimes (𝓝 L)) :
    Tendsto (fun p => imageError p (H p)) alongPrimes (𝓝 (L/6)) := by
  have den := (starts_asymptotic H low).2
  have num : Tendsto (fun p : ℕ => (H p:ℝ)*(H p+2)/p) alongPrimes (𝓝 L) := by
    convert sq.add ((tendsto_const_nhds (x:=(2:ℝ))).mul low) using 1
    · funext p; ring
    · simp
  have lim := (num.div den (by norm_num : (1:ℝ)≠0)).div_const 6
  apply (show Tendsto _ _ (𝓝 (L/6)) from by simpa using lim).congr'
  filter_upwards [eventually_prime] with p hp
  change ((H p:ℝ)*(H p+2)/p)/(((starts p (H p)).card:ℝ)/p)/6=_
  rw [div_div_div_cancel_right₀ (by exact_mod_cast hp.ne_zero : (p:ℝ)≠0)]
  unfold imageError
  ring

theorem subsquare_mean_image (H : ℕ → ℕ)
    (small : Tendsto (fun p => (H p:ℝ)^2/p) alongPrimes (𝓝 0)) :
    Tendsto (fun p => meanImageFraction p (H p)) alongPrimes (𝓝 1) := by
  have low : Tendsto (fun p => (H p:ℝ)/p) alongPrimes (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun p => by positivity) _ small
    exact Eventually.of_forall fun p => div_le_div_of_nonneg_right
      (by exact_mod_cast (Nat.le_pow (a:=H p) (by decide : 0<2))) (by positivity)
  have err : Tendsto (fun p => imageError p (H p)) alongPrimes (𝓝 0) := by
    simpa using error_limit H 0 low small
  have lb : Tendsto (fun p => 1-imageError p (H p)) alongPrimes (𝓝 1) := by
    simpa using (tendsto_const_nhds (x:=(1:ℝ))).sub err
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lb tendsto_const_nhds _ (Eventually.of_forall fun p => meanImage_le_one ..)
  filter_upwards [eventually_prime,(starts_asymptotic H low).1] with p hp fits
  have h := normalized_image_lower hp fits 1
  norm_num [show (1+1).choose 2=1 by decide] at h
  unfold imageError
  linarith only [h]

private theorem critical_inputs (H : ℕ → ℕ) (c : ℝ)
    (scale : Tendsto (fun p => (H p:ℝ)/Real.sqrt p) alongPrimes (𝓝 c)) :
    Tendsto (fun p => (H p:ℝ)/p) alongPrimes (𝓝 0) ∧
    Tendsto (fun p => (H p:ℝ)^2/p) alongPrimes (𝓝 (c^2)) := by
  have sr := (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).mono_left
    (show alongPrimes≤atTop from inf_le_left)
  have square (p : ℕ) := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) p)
  constructor
  · have h := scale.mul sr.inv_tendsto_atTop
    rw [mul_zero] at h
    apply h.congr'
    exact Eventually.of_forall fun p => by
      change (H p:ℝ)/Real.sqrt p*(Real.sqrt p)⁻¹=(H p:ℝ)/p
      rw [← div_eq_mul_inv,div_div,← pow_two,square]
  · simpa only [Pi.pow_apply,div_pow,square] using scale.pow 2

/-- This family of lower bounds is positive for suitable integer slopes at
every finite critical scale, including scales where the slope-one bound vanishes. -/
theorem critical_mean_image (H : ℕ → ℕ) (c t : ℝ) (m : ℕ)
    (scale : Tendsto (fun p => (H p:ℝ)/Real.sqrt p) alongPrimes (𝓝 c))
    (margin : ((m+1).choose 2:ℕ)*t+c^2/6<m) :
    ∀ᶠ p in alongPrimes, t<meanImageFraction p (H p) := by
  obtain ⟨low,sq⟩ := critical_inputs H c scale
  have err := error_limit H (c^2) low sq
  have bound := err.eventually_lt_const (show c^2/6<(m:ℝ)-((m+1).choose 2:ℕ)*t by linarith)
  filter_upwards [eventually_prime,(starts_asymptotic H low).1,bound] with p hp fits h
  have cert := normalized_image_lower hp fits m
  change (m:ℝ)≤_+imageError p (H p) at cert
  by_contra! bad
  exact (not_lt_of_ge (mul_le_mul_of_nonneg_left bad (by positivity : (0:ℝ)≤((m+1).choose 2:ℕ)))) (by linarith only [cert,h])

theorem critical_positive_density (H : ℕ → ℕ) (c : ℝ)
    (scale : Tendsto (fun p => (H p:ℝ)/Real.sqrt p) alongPrimes (𝓝 c)) :
    ∃ t : ℝ, 0<t ∧ ∀ᶠ p in alongPrimes, t<meanImageFraction p (H p) := by
  obtain ⟨m,hm⟩ := exists_nat_gt (c^2/6+1)
  have mp : 1≤m := by
    by_contra! no
    have : m=0 := by omega
    rw [this,Nat.cast_zero] at hm
    nlinarith [sq_nonneg c]
  let B : ℝ := (m+1).choose 2
  have bp : 0<B := by dsimp [B]; exact_mod_cast Nat.choose_pos (by omega : 2≤m+1)
  refine ⟨1/B,by positivity,critical_mean_image H c (1/B) m scale ?_⟩
  change B*(1/B)+c^2/6<m
  field_simp [bp.ne']
  linarith only [hm]

#print axioms imageError
#print axioms subsquare_mean_image
#print axioms critical_mean_image
#print axioms critical_positive_density
end
end Erdos478.WindowAverage
