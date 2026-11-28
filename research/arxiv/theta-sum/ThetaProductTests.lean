import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-! Real separable tests determine weak convergence on the real plane. -/
namespace Arxiv.«2501.03234».ThetaProductTests
open MeasureTheory Filter BoundedContinuousFunction WithLp
open scoped Topology
noncomputable section

private def tensor {K : Type*} [RCLike K] (u v : ℝ →ᵇ K) : (ℝ×ℝ) →ᵇ K :=
  u.compContinuous ⟨Prod.fst,continuous_fst⟩ * v.compContinuous ⟨Prod.snd,continuous_snd⟩
private def re (u : ℝ →ᵇ ℂ) : ℝ →ᵇ ℝ := comp Complex.re Complex.reCLM.lipschitz u
private def im (u : ℝ →ᵇ ℂ) : ℝ →ᵇ ℝ := comp Complex.im Complex.imCLM.lipschitz u

def val {K : Type*} [RCLike K] (m : ProbabilityMeasure (ℝ×ℝ)) (u v : ℝ →ᵇ K) :=
  ∫ z : ℝ×ℝ, u z.1*v z.2 ∂(m : Measure (ℝ×ℝ))

private theorem real_part (m : ProbabilityMeasure (ℝ×ℝ)) (u v : ℝ →ᵇ ℂ) :
    (val m u v).re = val m (re u) (re v) - val m (im u) (im v) := by
  have h := (tensor u v).integrable (m:Measure (ℝ×ℝ))
  change Integrable (fun z : ℝ×ℝ => u z.1 * v z.2) (m:Measure (ℝ×ℝ)) at h
  change RCLike.re (∫ z : ℝ×ℝ, u z.1*v z.2 ∂(m:Measure (ℝ×ℝ)))=_
  rw [← integral_re h]
  change (∫ z : ℝ×ℝ, (u z.1*v z.2).re ∂(m:Measure (ℝ×ℝ)))=_
  simp_rw [Complex.mul_re]
  exact integral_sub ((tensor (re u) (re v)).integrable _) ((tensor (im u) (im v)).integrable _)

private theorem imag_part (m : ProbabilityMeasure (ℝ×ℝ)) (u v : ℝ →ᵇ ℂ) :
    (val m u v).im = val m (re u) (im v) + val m (im u) (re v) := by
  have h := (tensor u v).integrable (m:Measure (ℝ×ℝ))
  change Integrable (fun z : ℝ×ℝ => u z.1 * v z.2) (m:Measure (ℝ×ℝ)) at h
  change RCLike.im (∫ z : ℝ×ℝ, u z.1*v z.2 ∂(m:Measure (ℝ×ℝ)))=_
  rw [← integral_im h]
  change (∫ z : ℝ×ℝ, (u z.1*v z.2).im ∂(m:Measure (ℝ×ℝ)))=_
  simp_rw [Complex.mul_im]
  exact integral_add ((tensor (re u) (im v)).integrable _) ((tensor (im u) (re v)).integrable _)

theorem complex {m : ℕ → ProbabilityMeasure (ℝ×ℝ)} {m₀ : ProbabilityMeasure (ℝ×ℝ)}
    (h : ∀ u v : ℝ →ᵇ ℝ,Tendsto (fun n => val (m n) u v) atTop (𝓝 (val m₀ u v))) (u v : ℝ →ᵇ ℂ) :
    Tendsto (fun n => val (m n) u v) atTop (𝓝 (val m₀ u v)) := by
  have hr : Tendsto (fun n => (val (m n) u v).re) atTop (𝓝 (val m₀ u v).re) := by
    simp only [real_part];exact (h _ _).sub (h _ _)
  have hi : Tendsto (fun n => (val (m n) u v).im) atTop (𝓝 (val m₀ u v).im) := by
    simp only [imag_part];exact (h _ _).add (h _ _)
  have H := ((Complex.continuous_ofReal.tendsto _).comp hr).add (((Complex.continuous_ofReal.tendsto _).comp hi).mul_const Complex.I)
  simpa only [Function.comp_apply,Complex.re_add_im] using H

private def lift (m : ProbabilityMeasure (ℝ×ℝ)) : ProbabilityMeasure (WithLp 2 (ℝ×ℝ)) :=
  m.map (prod_continuous_toLp 2 ℝ ℝ).measurable.aemeasurable

private theorem char (m : ProbabilityMeasure (ℝ×ℝ)) (t : WithLp 2 (ℝ×ℝ)) :
    charFun (lift m : Measure (WithLp 2 (ℝ×ℝ))) t =
    val m (innerProbChar (ofLp t).1) (innerProbChar (ofLp t).2) := by
  simp only [lift,ProbabilityMeasure.toMeasure_map,charFun_apply]
  rw [integral_map (prod_continuous_toLp 2 ℝ ℝ).measurable.aemeasurable (by fun_prop)]
  simp [val,prod_inner_apply,innerProbChar_apply,add_mul,Complex.exp_add]

theorem weak {m : ℕ → ProbabilityMeasure (ℝ×ℝ)} {m₀ : ProbabilityMeasure (ℝ×ℝ)}
    (h : ∀ u v : ℝ →ᵇ ℝ,Tendsto (fun n => val (m n) u v) atTop (𝓝 (val m₀ u v))) :
    Tendsto m atTop (𝓝 m₀) := by
  have hl : Tendsto (fun n => lift (m n)) atTop (𝓝 (lift m₀)) := by
    apply ProbabilityMeasure.tendsto_of_tendsto_charFun
    intro t
    simp only [char]
    exact complex h _ _
  have hh := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hl (prod_continuous_ofLp 2 ℝ ℝ)
  have eqn (ν : ProbabilityMeasure (ℝ×ℝ)) :
      (lift ν).map (prod_continuous_ofLp 2 ℝ ℝ).measurable.aemeasurable=ν := by
    apply Subtype.ext
    simp only [ProbabilityMeasure.val_eq_to_measure,lift,ProbabilityMeasure.toMeasure_map,Measure.map_map
      (prod_continuous_ofLp 2 ℝ ℝ).measurable (prod_continuous_toLp 2 ℝ ℝ).measurable]
    exact Measure.map_id
  simpa only [eqn] using hh

#print axioms weak
end
end Arxiv.«2501.03234».ThetaProductTests
