import Green51DefectGrowthBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Leading quadratic exponent of the stable Green 51 class number -/
namespace Green51FrameIsomorphisms
open Filter Real
open scoped Topology

theorem log_growth_error {h : ℕ} (large : 10≤h) :
    |Real.log (universalDefectNumber h) - (h:ℝ)^2 * Real.log 2/4| ≤
      (h:ℝ)*Real.log h+4*h := by
  have low := lower_growth large
  have up := upper_growth h
  have posN : 0<universalDefectNumber h := by
    by_contra! fail
    have e : universalDefectNumber h=0 := by omega
    simp [e] at low
  have hp : (0:ℝ)<h := by exact_mod_cast (show 0<h by omega)
  have pn : (0:ℝ)<universalDefectNumber h := by exact_mod_cast posN
  have l : (2:ℝ)^(h*h/4) ≤ (universalDefectNumber h:ℝ)*h^h*2^(h+h/2) := by exact_mod_cast low
  have u : (universalDefectNumber h:ℝ) ≤ (h:ℝ)^h*(h+1)*2^(h*h/4+h) := by exact_mod_cast up
  have ll := Real.log_le_log (by positivity) l
  have uu := Real.log_le_log pn u
  simp (disch := positivity) only [Real.log_mul,Real.log_pow,Nat.cast_add] at ll uu
  have fa : 4*(h*h/4) ≤ h*h := by omega
  have fb : h*h ≤ 4*(h*h/4)+3 := by omega
  have loF : (4:ℝ)*(h*h/4:ℕ)≤(h:ℝ)*h := by exact_mod_cast fa
  have hiF : (h:ℝ)*h≤4*(h*h/4:ℕ)+3 := by exact_mod_cast fb
  have half : (h/2:ℕ)≤(h:ℝ) := by exact_mod_cast (show h/2≤h by omega)
  have logp : 0<Real.log 2 := Real.log_pos (by norm_num)
  have logle : Real.log 2≤1 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have logH := Real.log_le_sub_one_of_pos (by positivity : 0<(h:ℝ)+1)
  have hl : (10:ℝ)≤h := by exact_mod_cast large
  apply abs_le.mpr
  constructor
  · nlinarith only [ll,mul_le_mul_of_nonneg_right hiF logp.le,mul_le_mul_of_nonneg_right half logp.le,
      mul_le_mul_of_nonneg_left logle hp.le,logle,hl]
  · nlinarith only [uu,logH,mul_le_mul_of_nonneg_right loF logp.le,mul_le_mul_of_nonneg_left logle hp.le,hp]

theorem universal_quadratic_rate :
    Tendsto (fun h : ℕ => Real.logb 2 (universalDefectNumber h)/(h:ℝ)^2)
      atTop (𝓝 (1/4 : ℝ)) := by
  have logTerm : Tendsto (fun h : ℕ => Real.log (h:ℝ)/h) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have small : Tendsto (fun h : ℕ => Real.log (h:ℝ)/h+4*(1/h)) atTop (𝓝 0) := by
    simpa using logTerm.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ) |>.const_mul 4)
  have main : Tendsto (fun h : ℕ => Real.log (universalDefectNumber h)/(h:ℝ)^2)
      atTop (𝓝 (Real.log 2/4)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) _ small
    filter_upwards [eventually_ge_atTop 10] with h hh
    have err := log_growth_error hh
    have hp : (0:ℝ)<h := by exact_mod_cast (show 0<h by omega)
    rw [Real.dist_eq,show Real.log (universalDefectNumber h)/(h:ℝ)^2-Real.log 2/4 =
       (Real.log (universalDefectNumber h)-(h:ℝ)^2*Real.log 2/4)/(h:ℝ)^2 by field_simp,
       abs_div,abs_of_nonneg (sq_nonneg (h:ℝ)),div_le_iff₀ (by positivity)]
    calc
      _ ≤ (h:ℝ)*Real.log h+4*h := err
      _ = _ := by field_simp
  have p : Real.log 2≠0 := (Real.log_pos (by norm_num : (1:ℝ)<2)).ne'
  convert main.div_const (Real.log 2) using 1
  · ext h
    rw [Real.logb]
    ring
  · field_simp

/-- The same rate holds for actual sumsets along every admissible sequence of dimensions. -/
theorem dense_quadratic_rate (s r : ℕ → ℕ)
    (room : ∀ᶠ (h : ℕ) in atTop, 5 ≤ s h ∧ h ≤ 2*s h+3 ∧ h < 2^(r h) ∧ h-1 ≤ r h) :
    Tendsto (fun h : ℕ => Real.logb 2 (fibreClasses (s h) (r h) h)/(h:ℝ)^2)
      atTop (𝓝 (1/4 : ℝ)) := by
  apply universal_quadratic_rate.congr'
  filter_upwards [room] with h hh
  rw [stable_dense_number hh.1 hh.2.1 hh.2.2.1 hh.2.2.2]

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.log_growth_error
#print axioms Green51FrameIsomorphisms.universal_quadratic_rate
#print axioms Green51FrameIsomorphisms.dense_quadratic_rate
