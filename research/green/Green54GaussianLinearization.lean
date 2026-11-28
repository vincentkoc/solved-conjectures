import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Mean-square convergence of Gaussian directional difference quotients for Lipschitz maps. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
namespace Green54GaussianLinearization

private theorem pi_const_ac {V : Type*} [MeasurableSpace V] (μ ν : Measure V) [SigmaFinite μ]
    [SigmaFinite ν] (h : μ ≪ ν) (ι : Type*) [Fintype ι] :
    (Measure.pi fun _ : ι => μ) ≪ Measure.pi fun _ : ι => ν := by
  have hfin (n : ℕ) : (Measure.pi fun _ : Fin n => μ) ≪ Measure.pi fun _ : Fin n => ν := by
    induction n with
    | zero =>
      rw [Measure.pi_of_empty (fun _ : Fin 0 => μ) Fin.elim0,
        Measure.pi_of_empty (fun _ : Fin 0 => ν) Fin.elim0]
    | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => V) (Fin.last n)
      have heμ := (measurePreserving_piFinSuccAbove (fun _ => μ) (Fin.last n)).symm.map_eq
      have heν := (measurePreserving_piFinSuccAbove (fun _ => ν) (Fin.last n)).symm.map_eq
      rw [← heμ, ← heν]
      exact (h.prod ih).map e.symm.measurable
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft (fun _ : ι => μ) e).map_eq,
    ← (measurePreserving_piCongrLeft (fun _ : ι => ν) e).map_eq]
  exact (hfin _).map (MeasurableEquiv.piCongrLeft _ e).measurable

variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The standard finite-dimensional Gaussian is absolutely continuous with respect to volume. -/
theorem gaussian_ac_volume : stdGaussian E ≪ volume := by
  rw [← map_pi_eq_stdGaussian, ← (PiLp.volume_preserving_toLp ι).map_eq]
  exact (pi_const_ac (gaussianReal 0 1) volume (gaussianReal_absolutelyContinuous 0 one_ne_zero) ι).map
    (PiLp.continuous_toLp 2 _).measurable

/-- Gaussian-almost-everywhere directional linearization of a Lipschitz map. -/
theorem ae_slopes {T : E → E} {K : ℝ≥0} (hT : LipschitzWith K T) :
    ∀ᵐ x ∂stdGaussian E, ∀ v : E, Tendsto
      (fun t : ℝ => t⁻¹ • (T (x + t • v) - T x)) (𝓝[≠] 0) (𝓝 (fderiv ℝ T x v)) := by
  filter_upwards [gaussian_ac_volume.ae_le hT.ae_differentiableAt] with x hx
  exact fun v => (hx.hasFDerivAt.hasLineDerivAt v).tendsto_slope_zero


/-- Error of the directional difference quotient at the sampled point and direction. -/
def slopeError (T : E → E) (t : ℝ) (z : E × E) : E :=
  t⁻¹ • (T (z.1 + t • z.2) - T z.1) - fderiv ℝ T z.1 z.2

/-- A Lipschitz bound controls both terms in the directional approximation. -/
theorem slopeError_bound {T : E → E} {K : ℝ≥0} (hT : LipschitzWith K T)
    (t : ℝ) (z : E × E) : ‖slopeError T t z‖ ≤ 2 * K * ‖z.2‖ := by
  have hD : ‖fderiv ℝ T z.1 z.2‖ ≤ K * ‖z.2‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (norm_fderiv_le_of_lipschitz ℝ hT) (norm_nonneg _))
  have hS : ‖t⁻¹ • (T (z.1 + t • z.2) - T z.1)‖ ≤ K * ‖z.2‖ := by
    by_cases ht : t = 0
    · simp [ht, mul_nonneg K.coe_nonneg (norm_nonneg z.2)]
    rw [norm_smul, norm_inv]
    have hl := hT.norm_sub_le (z.1 + t • z.2) z.1
    rw [add_sub_cancel_left, norm_smul] at hl
    calc
      _ ≤ ‖t‖⁻¹ * (K * (‖t‖ * ‖z.2‖)) := mul_le_mul_of_nonneg_left hl (by positivity)
      _ = _ := by field_simp
  exact (norm_sub_le _ _).trans (by linarith)

omit [Fintype ι] in
theorem scaled_slopeError (T : E → E) (t : ℝ) (z v : E) :
    t • slopeError T t (z,v) = T (z+t • v) - T z - t • fderiv ℝ T z v := by
  by_cases ht : t = 0
  · simp [ht]
  · simp [slopeError, smul_sub, smul_smul, ht]

theorem measurable_slopeError {T : E → E} {K : ℝ≥0} (hT : LipschitzWith K T) (t : ℝ) :
    Measurable (slopeError T t) := by
  have heval : Continuous (fun z : (E →L[ℝ] E) × E => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  have hD : Measurable (fun z : E × E => fderiv ℝ T z.1 z.2) :=
    heval.measurable.comp (((measurable_fderiv ℝ T).comp measurable_fst).prodMk measurable_snd)
  have hTm := hT.continuous.measurable
  unfold slopeError
  fun_prop

/-- The Gaussian mean squared linearization error, divided by the squared step size,
tends to zero for every Lipschitz map in every finite dimension. -/
theorem mean_square_slopes {T : E → E} {K : ℝ≥0} (hT : LipschitzWith K T) :
    Tendsto (fun t => ∫ z, ‖slopeError T t z‖ ^ 2 ∂(stdGaussian E).prod (stdGaussian E))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  let γ := stdGaussian E
  have hmeas (t : ℝ) : Measurable (fun z : E × E => ‖slopeError T t z‖ ^ 2) := by
    exact (measurable_slopeError hT t).norm.pow_const 2
  have hnorm : Integrable (fun v : E => ‖v‖ ^ 2) γ := IsGaussian.memLp_two_id.norm.integrable_sq
  have hbound : Integrable (fun z : E × E => (2 * (K : ℝ) * ‖z.2‖) ^ 2) (γ.prod γ) := by
    simp only [mul_pow]
    exact (measurePreserving_snd.integrable_comp_of_integrable hnorm).const_mul _
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := γ.prod γ)
    (f := fun _ : E × E => (0 : ℝ)) (F := fun t z => ‖slopeError T t z‖ ^ 2)
    (l := 𝓝[≠] (0 : ℝ)) (fun z => (2 * (K : ℝ) * ‖z.2‖)^2)
    (.of_forall fun t => (hmeas t).aestronglyMeasurable)
    (.of_forall fun t => ae_of_all _ fun z => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (slopeError_bound hT t z) 2)
    hbound (by
      filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae (ae_slopes hT)] with z hz
      simpa [slopeError] using (((hz z.2).sub (tendsto_const_nhds (x := fderiv ℝ T z.1 z.2))).norm.pow 2))
  simpa [γ] using hlim

#print axioms gaussian_ac_volume
#print axioms slopeError_bound
#print axioms scaled_slopeError
#print axioms measurable_slopeError
#print axioms ae_slopes
#print axioms mean_square_slopes
end Green54GaussianLinearization
