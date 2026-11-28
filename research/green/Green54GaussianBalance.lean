import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Bounds on a one-step stationarity error from the forward and time-reversed pair densities. -/

open MeasureTheory
open scoped RealInnerProductSpace
namespace Green54GaussianBalance
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Trapezoid error for a differentiable convex potential, from its supporting affine functions. -/
theorem trapezoid_error {U : E → ℝ} {G : E → E} {L : NNReal} (hL : LipschitzWith L G)
    (hsub : ∀ x y, ⟪G x,y-x⟫ ≤ U y-U x) (x y : E) :
    |U y-U x - (⟪G x,y-x⟫+⟪G y,y-x⟫)/2| ≤ (L:ℝ)/2 * ‖y-x‖^2 := by
  have hl := hsub x y
  have hu := hsub y x
  rw [← neg_sub y x, inner_neg_right] at hu
  have hc := (real_inner_le_norm (G y-G x) (y-x)).trans
    (mul_le_mul_of_nonneg_right (hL.norm_sub_le y x) (norm_nonneg _))
  rw [inner_sub_left] at hc
  exact abs_le.mpr (by constructor <;> nlinarith)

/-- The asymmetry of the two Gaussian proposal exponents for a gradient step. -/
theorem proposal_difference (U : E → ℝ) (G : E → E) {h : ℝ} (hh : h ≠ 0) (x y : E) :
    (-U x - ‖(y-x)+h • G x‖^2/(4*h)) - (-U y - ‖(x-y)+h • G y‖^2/(4*h)) =
      U y-U x - (⟪G x,y-x⟫+⟪G y,y-x⟫)/2 + h/4*(‖G y‖^2-‖G x‖^2) := by
  rw [show x-y = -(y-x) from (neg_sub y x).symm]
  simp only [norm_add_sq_real, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_smul_right, inner_neg_left]
  rw [real_inner_comm (y-x) (G x), real_inner_comm (y-x) (G y)]
  field_simp
  ring

private theorem acceptance_est {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a - min a b ≤ a * |Real.log a - Real.log b| := by
  rcases le_total a b with h | h
  · rw [min_eq_left h,sub_self]
    positivity
  · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hb h))]
    have hlog := Real.log_le_sub_one_of_pos (div_pos hb ha)
    rw [Real.log_div hb.ne' ha.ne'] at hlog
    have := mul_le_mul_of_nonneg_left hlog ha.le
    field_simp [ha.ne'] at this
    nlinarith

section
variable {V : Type*} [MeasurableSpace V] {μ : Measure V} [SFinite μ]
/-- The antisymmetric test integral is controlled by the log ratio of the joint density and its reverse. -/
theorem balance_error (a : V × V → ℝ) (F : V → ℝ) (ha : ∀ z, 0 < a z)
    (hd : Integrable (fun z : V × V => a z * (F z.2-F z.1)) (μ.prod μ))
    (hm : Integrable (fun z : V × V => min (a z) (a z.swap) * (F z.2-F z.1)) (μ.prod μ))
    (hb : Integrable (fun z : V × V => a z * |Real.log (a z) - Real.log (a z.swap)| *
      |F z.2 - F z.1|) (μ.prod μ)) :
    |∫ z, a z * (F z.2-F z.1) ∂μ.prod μ| ≤
      ∫ z, a z * |Real.log (a z) - Real.log (a z.swap)| * |F z.2-F z.1| ∂μ.prod μ := by
  let m (z : V × V) := min (a z) (a z.swap) * (F z.2-F z.1)
  have hm0 : (∫ z, m z ∂μ.prod μ) = 0 := by
    have h := integral_prod_swap (μ := μ) (ν := μ) m
    have he (z : V × V) : m z.swap = -m z := by simp only [m,Prod.swap_swap, Prod.fst_swap,Prod.snd_swap];rw [min_comm];ring
    simp only [he,integral_neg] at h
    linarith
  rw [← sub_zero (∫ z, a z * (F z.2-F z.1) ∂μ.prod μ), ← hm0, ← integral_sub hd hm, ← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le hb (ae_of_all _ fun z => ?_)
  change ‖a z * (F z.2-F z.1) - min (a z) (a z.swap) * (F z.2-F z.1)‖ ≤ _
  rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr (min_le_left _ _))]
  exact mul_le_mul_of_nonneg_right (acceptance_est (ha z) (ha z.swap)) (abs_nonneg _)
end

omit [InnerProductSpace ℝ E] in
private theorem score_square_difference {G : E → E} {L : NNReal} (hL : LipschitzWith L G) (x y : E) :
    |‖G y‖^2-‖G x‖^2| ≤ (L:ℝ)*‖y-x‖*(2*‖G x‖+(L:ℝ)*‖y-x‖) := by
  rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hn := abs_norm_sub_norm_le (G y) (G x)
  have hu := (norm_sub_norm_le (G y) (G x)).trans (hL.norm_sub_le y x)
  rw [mul_comm (‖G y‖ + ‖G x‖)]
  exact mul_le_mul (hn.trans (hL.norm_sub_le y x)) (by linarith) (by positivity) (by positivity)

/-- A dimension-independent pointwise bound on the time-reversal error of a Langevin step. -/
theorem proposal_log_error {U : E → ℝ} {G : E → E} {L : NNReal} (hL : LipschitzWith L G)
    (hsub : ∀ x y, ⟪G x,y-x⟫ ≤ U y-U x) {h : ℝ} (hh : 0 < h) (x y : E) :
    |(-U x - ‖(y-x)+h • G x‖^2/(4*h)) - (-U y - ‖(x-y)+h • G y‖^2/(4*h))| ≤
    (L:ℝ)/2*‖y-x‖^2 + h/4*((L:ℝ)*‖y-x‖*(2*‖G x‖+(L:ℝ)*‖y-x‖)) := by
  rw [proposal_difference U G hh.ne']
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ h/4)]
  exact add_le_add (trapezoid_error hL hsub x y)
    (mul_le_mul_of_nonneg_left (score_square_difference hL x y) (by positivity))


private theorem cubic_cost {t B a d L : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hB : 0 ≤ B) (hd : 0 ≤ d) (ha : a ≤ B) (hL : 0 ≤ L) (hdt : d ≤ t*B) :
    d*(L/2*d^2 + t^2/4*(L*d*(2*a+L*d))) ≤
      (L/2 + L/4*(2+L))*t^3*B^3 := by
  have hD := hdt.trans (by nlinarith [mul_le_mul_of_nonneg_right ht1 hB] : t*B ≤ B)
  have hd3 : d^3 ≤ t^3*B^3 := by simpa only [mul_pow] using pow_le_pow_left₀ hd hdt 3
  have hd2 : d^2 ≤ t^2*B^2 := by simpa only [mul_pow] using pow_le_pow_left₀ hd hdt 2
  have h4 : t^2*d^2 ≤ t^3*B^2 := by
    calc
      _ ≤ t^2*(t^2*B^2) := mul_le_mul_of_nonneg_left hd2 (sq_nonneg _)
      _ = (t^3*B^2)*t := by ring
      _ ≤ t^3*B^2 := by exact (mul_le_mul_of_nonneg_left ht1 (by positivity)).trans_eq (mul_one _)
  have hl : 2*a+L*d ≤ (2+L)*B := by nlinarith [mul_le_mul_of_nonneg_left hD hL]
  calc
    _ = L/2*d^3 + L/4*((2*a+L*d)*(t^2*d^2)) := by ring
    _ ≤ L/2*(t^3*B^3) + L/4*(((2+L)*B)*(t^3*B^2)) :=
      add_le_add (mul_le_mul_of_nonneg_left hd3 (by positivity))
        (mul_le_mul_of_nonneg_left (mul_le_mul hl h4 (by positivity) (by positivity)) (by positivity))
    _ = _ := by ring

/-- Along an Euler proposal, the distance-weighted log-ratio costs at most a fixed cubic
moment times the step size to the power three halves. -/
theorem proposal_cubic_error {U : E → ℝ} {G : E → E} {L : NNReal} (hL : LipschitzWith L G)
    (hsub : ∀ x y, ⟪G x,y-x⟫ ≤ U y-U x) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (x z : E) :
    let y := x - h • G x + Real.sqrt (2*h) • z
    ‖y-x‖ * |(-U x - ‖(y-x)+h • G x‖^2/(4*h)) - (-U y - ‖(x-y)+h • G y‖^2/(4*h))| ≤
      ((L:ℝ)/2 + L/4*(2+L))*(Real.sqrt h)^3*(‖G x‖+2*‖z‖)^3 := by
  let y := x - h • G x + Real.sqrt (2*h) • z
  let t := Real.sqrt h
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have ht1 : t ≤ 1 := (Real.sqrt_le_one).mpr hh1
  have ht2 : t^2 = h := Real.sq_sqrt hh.le
  have hht : h ≤ t := by nlinarith [mul_le_mul_of_nonneg_left ht1 ht]
  have hs : Real.sqrt (2*h) ≤ 2*t := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_right (by norm_num) ht
  have hy : y-x = -(h • G x) + Real.sqrt (2*h) • z := by unfold y; abel
  have hd : ‖y-x‖ ≤ t*(‖G x‖+2*‖z‖) := by
    rw [hy]
    apply (norm_add_le _ _).trans
    rw [norm_neg,norm_smul,norm_smul,Real.norm_of_nonneg hh.le,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [mul_le_mul_of_nonneg_right hht (norm_nonneg (G x)),
      mul_le_mul_of_nonneg_right hs (norm_nonneg z)]
  have he := mul_le_mul_of_nonneg_left (proposal_log_error hL hsub hh x y) (norm_nonneg (y-x))
  apply he.trans
  have hc := cubic_cost (L := (L:ℝ)) ht ht1 (by positivity) (norm_nonneg (y-x))
    (show ‖G x‖ ≤ ‖G x‖+2*‖z‖ from le_add_of_nonneg_right (by positivity)) L.coe_nonneg hd
  simpa only [ht2] using hc

#print axioms proposal_cubic_error
#print axioms proposal_log_error
#print axioms trapezoid_error
#print axioms proposal_difference
#print axioms balance_error
end Green54GaussianBalance
