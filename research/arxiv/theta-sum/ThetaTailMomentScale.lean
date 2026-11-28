import ThetaDoubleExponentialLaw
import ThetaResidualMoments

/-! Moment bounds from the double-exponential tails of the limiting law. -/
namespace Arxiv.«2501.03234».ThetaTailMomentScale
open Real Filter Finset MeasureTheory ThetaDoubleExponentialLaw ThetaDiagonalConstant
open scoped Topology
noncomputable section

theorem upper_at {μ : ProbabilityMeasure ℝ} {c b : ℝ} (hb : 0<b)
    (hl : 1≤c*sqrt b) {k : ℕ} (hk : 0<k) (hsize : 4*(k:ℝ)≤exp (c*sqrt b))
    (h : ∀ t≥b, (μ:Measure ℝ) (outside t) ≤ ENNReal.ofReal (exp (-exp (c*sqrt t)))) :
    Integrable (fun x => |x-diagonalConstant|^k) (μ:Measure ℝ) ∧
      (∫ x, |x-diagonalConstant|^k ∂(μ:Measure ℝ)) ≤ 2*b^k := by
  let A (x : ℝ) := max 1 (|x-diagonalConstant|/b)
  let U (x : ℝ) := (k:ℝ)*log (A x)
  have hk' : (0:ℝ)<k := Nat.cast_pos.mpr hk
  have hA x : 1≤A x := le_max_left ..
  have hpos x : 0<A x := lt_of_lt_of_le zero_lt_one (hA x)
  have hcont : Continuous U := by
    have hA' : Continuous A := by dsimp [A];fun_prop
    exact continuous_const.mul (hA'.log (fun x => (hpos x).ne'))
  have hnon x : 0≤U x := mul_nonneg hk'.le (log_nonneg (hA x))
  have H {t : ℝ} (ht : 0≤t) :
      (μ:Measure ℝ) {x : ℝ | t < U x} ≤ ENNReal.ofReal (1*exp (-2*t)) := by
    let y := exp (t/(2*k))
    have hy : 1≤y := one_le_exp (by positivity)
    have hys : y^2=exp (t/k) := by
      dsimp only [y];rw [sq,← exp_add];congr 1;ring
    have hby : b≤b*y^2 := by nlinarith only [mul_le_mul_of_nonneg_left (one_le_pow₀ hy (n:=2)) hb.le]
    have hs : sqrt (b*y^2)=sqrt b*y := by rw [sqrt_mul hb.le,sqrt_sq (by linarith : 0≤y)]
    have hsub : {x : ℝ | t < U x}⊆outside (b*y^2) := by
      intro x hx
      have htlog : t/k < log (A x) := (div_lt_iff₀ hk').mpr (by change t < (k:ℝ)*log (A x) at hx;linarith)
      have hv := exp_lt_exp.mpr htlog
      rw [exp_log (hpos x)] at hv
      have hratio := (lt_max_iff.mp hv).resolve_left (not_lt.mpr (one_le_exp (div_nonneg ht hk'.le)))
      change b*y^2 < |x-diagonalConstant|
      rw [hys];linarith only [(lt_div_iff₀ hb).mp hratio]
    have hz : 0≤t/(2*k) := by positivity
    have hex : c*sqrt b+t/(2*k)≤c*sqrt b*y := by
      have h₁ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (t/(2*k))) (by linarith : 0≤c*sqrt b)
      nlinarith only [h₁,mul_le_mul_of_nonneg_right hl hz]
    have hv : 2*t ≤ exp (c*sqrt b*y) := calc
      2*t = (4*(k:ℝ))*(t/(2*k)) := by field_simp;ring
      _ ≤ exp (c*sqrt b)*exp (t/(2*k)) :=
        mul_le_mul hsize (by linarith only [Real.add_one_le_exp (t/(2*k))]) hz (exp_pos _).le
      _ ≤ _ := by rw [← exp_add];exact exp_le_exp.mpr hex
    apply ((measure_mono hsub).trans (h _ hby)).trans
    apply ENNReal.ofReal_le_ofReal
    rw [hs,← mul_assoc,one_mul]
    exact exp_le_exp.mpr (by linarith)
  obtain ⟨hi,hint⟩ := ThetaResidualMoments.exp_moment_of_tail (by norm_num : (0:ℝ)≤1) hcont hnon H
  have he (x : ℝ) : exp (U x)=A x^k := by dsimp [U];rw [Real.exp_nat_mul,exp_log (hpos x)]
  have hpoint (x : ℝ) : |x-diagonalConstant|^k ≤ b^k*exp (U x) := by
    rw [he,← mul_pow]
    apply pow_le_pow_left₀ (abs_nonneg _)
    have hq := le_max_right 1 (|x-diagonalConstant|/b)
    linarith only [(div_le_iff₀ hb).mp hq]
  have hg : Integrable (fun x : ℝ => |x-diagonalConstant|^k) (μ:Measure ℝ) :=
    (hi.const_mul (b^k)).mono' (by fun_prop)
      (Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using hpoint x))
  refine ⟨hg,(integral_mono hg (hi.const_mul (b^k)) hpoint).trans ?_⟩
  rw [integral_const_mul]
  linarith only [mul_le_mul_of_nonneg_left hint (pow_nonneg hb.le k)]

theorem lower_at {μ : ProbabilityMeasure ℝ} {b m : ℝ} (hb : 0≤b) (hm : 0≤ m)
    {k : ℕ} (hi : Integrable (fun x => |x-diagonalConstant|^k) (μ:Measure ℝ))
    (h : ENNReal.ofReal m ≤ (μ:Measure ℝ) (Set.Ioi (diagonalConstant+b))) :
    m*b^k ≤ ∫ x, |x-diagonalConstant|^k ∂(μ:Measure ℝ) := by
  let s := Set.Ioi (diagonalConstant+b)
  have hp : m≤(μ:Measure ℝ).real s := by
    rw [← ENNReal.toReal_ofReal hm]
    exact ENNReal.toReal_mono (measure_ne_top (μ:Measure ℝ) s) h
  calc
    _ ≤ (μ:Measure ℝ).real s*b^k := mul_le_mul_of_nonneg_right hp (pow_nonneg hb k)
    _ = ∫ _x in s, b^k ∂(μ:Measure ℝ) := by rw [setIntegral_const,smul_eq_mul]
    _ ≤ ∫ x in s, |x-diagonalConstant|^k ∂(μ:Measure ℝ) := by
      apply setIntegral_mono_on (integrable_const _).integrableOn hi.integrableOn measurableSet_Ioi
      intro x hx
      change diagonalConstant+b < x at hx
      exact pow_le_pow_left₀ hb (by linarith only [hx,le_abs_self (x-diagonalConstant)]) k
    _ ≤ _ := setIntegral_le_integral hi (Eventually.of_forall (fun x => pow_nonneg (abs_nonneg _) k))

#print axioms lower_at
#print axioms upper_at
end
end Arxiv.«2501.03234».ThetaTailMomentScale
