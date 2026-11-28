import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Densities of isotropic Gaussian transitions in a finite Euclidean space. -/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section
namespace Green54GaussianKernel
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

private theorem gaussian_pi_pdf (m : ι → ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (Measure.pi fun i => gaussianReal (m i) v) =
      (volume : Measure (ι → ℝ)).withDensity (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal (m i) v (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  change (∫⁻ x, ENNReal.ofReal (∏ i, gaussianPDFReal (m i) v (x i))
    ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))).restrict (univ.pi s)) = _
  rw [Measure.restrict_pi_pi]
  have hi (i : ι) : Integrable (gaussianPDFReal (m i) v) (volume.restrict (s i)) :=
    (integrable_gaussianPDFReal _ _).integrableOn
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod hi)
    (ae_of_all _ fun x => Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg _ _ _),
    integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg (fun i _ =>
      integral_nonneg fun z => gaussianPDFReal_nonneg (m i) v z)]
  simp only [gaussianReal_apply_eq_integral _ hv]

/-- Isotropic Gaussian density relative to Euclidean volume. -/
def gaussianDensity (m : E) (v : ℝ≥0) (x : E) : ℝ :=
  (Real.sqrt (2*Real.pi*v))⁻¹ ^ Fintype.card ι * Real.exp (-‖x-m‖^2/(2*v))

private theorem density_eq_prod (m : E) (v : ℝ≥0) (x : E) :
    gaussianDensity m v x = ∏ i, gaussianPDFReal (m i) v (x i) := by
  simp only [gaussianDensity, gaussianPDFReal_def, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, ← Real.exp_sum, ← Finset.sum_div, ← Finset.sum_neg_distrib,
    EuclideanSpace.real_norm_sq_eq]
  rfl

private theorem map_weighted {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {f : A → B} (hf : MeasurePreserving f μ ν)
    {g : B → ℝ≥0∞} (hg : Measurable g) :
    (μ.withDensity (fun a => g (f a))).map f = ν.withDensity g := by
  ext s hs
  rw [Measure.map_apply hf.measurable hs, withDensity_apply _ (hf.measurable hs), withDensity_apply _ hs,
    ← hf.map_eq, setLIntegral_map hs hg hf.measurable]

/-- The explicit proposal density of a scaled and shifted standard Gaussian. -/
theorem affine_gaussian_density (m : E) (σ : ℝ) (hs : σ ≠ 0) :
    let v : ℝ≥0 := ⟨σ^2,sq_nonneg _⟩
    (stdGaussian E).map (fun z => m + σ • z) =
      (volume : Measure E).withDensity (fun x => ENNReal.ofReal (gaussianDensity m v x)) := by
  let v : ℝ≥0 := ⟨σ^2,sq_nonneg _⟩
  let a (i : ι) (u : ℝ) := m i + σ*u
  let F (x : ι → ℝ) : ι → ℝ := fun i => a i (x i)
  have ha (i : ι) : Measurable (a i) := by unfold a; fun_prop
  have hF : Measurable F := measurable_pi_lambda _ (fun i => (ha _).comp (measurable_pi_apply _))
  have hmap (i : ι) : (gaussianReal 0 1).map (a i) = gaussianReal (m i) v := by
    change (gaussianReal 0 1).map ((fun x => m i+x) ∘ (fun x => σ*x)) = _
    rw [← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul, gaussianReal_map_const_add]
    simp [v]
    rfl
  have hi (i : ι) : IsProbabilityMeasure ((gaussianReal 0 1).map (a i)) :=
    Measure.isProbabilityMeasure_map (ha i).aemeasurable
  have hp : (Measure.pi fun _ : ι => gaussianReal 0 1).map F =
      Measure.pi (fun i => gaussianReal (m i) v) := by
    rw [show F = (fun x i => a i (x i)) from rfl, Measure.pi_map_pi (fun i => (ha i).aemeasurable)]
    simp only [hmap]
  have hv : v ≠ 0 := fun hv => (pow_ne_zero 2 hs) (congrArg (fun a : ℝ≥0 => (a : ℝ)) hv)
  let g (x : E) := ENNReal.ofReal (gaussianDensity m v x)
  have hm : Measurable g := by unfold g gaussianDensity; fun_prop
  have hd (z : ι → ℝ) : g (WithLp.toLp 2 z) = ENNReal.ofReal (∏ i, gaussianPDFReal (m i) v (z i)) := by
    simp only [g, density_eq_prod]
  change _ = (volume : Measure E).withDensity g
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (PiLp.continuous_toLp 2 _).measurable]
  calc
    _ = ((Measure.pi fun _ : ι => gaussianReal 0 1).map F).map (WithLp.toLp 2) :=
      (Measure.map_map (PiLp.continuous_toLp 2 _).measurable hF).symm
    _ = _ := by
      rw [hp, gaussian_pi_pdf _ hv, ← funext hd]
      exact map_weighted (PiLp.volume_preserving_toLp ι) hm

/-- The joint density of the old and proposed states from a random innovation. -/
theorem weighted_joint {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    (μ : Measure X) (γ : Measure Z) [SFinite μ] [SFinite γ]
    {p : X → ℝ≥0∞} (hp : Measurable p) {q : X × X → ℝ≥0∞} (hq : Measurable q)
    {F : X → Z → X} (hF : Measurable (Function.uncurry F))
    (hstep : ∀ x, γ.map (F x) = μ.withDensity (fun y => q (x,y))) :
    ((μ.withDensity p).prod γ).map (fun z : X × Z => (z.1,F z.1 z.2)) =
      (μ.prod μ).withDensity (fun z => p z.1*q z) := by
  let u (z : X × Z) := (z.1,F z.1 z.2)
  have hu : Measurable u := measurable_fst.prodMk hF
  have hw : Measurable (fun z : X × X => p z.1*q z) := (hp.comp measurable_fst).mul hq
  have he (f : X × X → ℝ≥0∞) (hf : Measurable f) :
      (∫⁻ z, f z ∂((μ.withDensity p).prod γ).map u) =
      ∫⁻ z, f z ∂(μ.prod μ).withDensity (fun z => p z.1*q z) := by
    have hum : Measurable (fun z => f (u z)) := hf.comp hu
    have hwm : Measurable (fun z => (p z.1*q z)*f z) := hw.mul hf
    rw [lintegral_map hf hu, lintegral_prod (fun z => f (u z)) hum.aemeasurable,
      lintegral_withDensity_eq_lintegral_mul _ hp hum.lintegral_prod_right',
      lintegral_withDensity_eq_lintegral_mul _ hw hf]
    change _ = ∫⁻ z, (p z.1*q z)*f z ∂μ.prod μ
    rw [lintegral_prod _ hwm.aemeasurable]
    apply lintegral_congr
    intro x
    have hf' : Measurable (fun y => f (x,y)) := hf.comp measurable_prodMk_left
    have hq' : Measurable (fun y => q (x,y)) := hq.comp measurable_prodMk_left
    have hF' : Measurable (F x) := hF.comp measurable_prodMk_left
    have hx := lintegral_map hf' hF' (μ := γ)
    rw [hstep, lintegral_withDensity_eq_lintegral_mul _ hq' hf'] at hx
    change p x * (∫⁻ z, f (x,F x z) ∂γ) = ∫⁻ y, p x * q (x,y) * f (x,y) ∂μ
    rw [← hx]
    simp only [mul_assoc]
    exact (lintegral_const_mul (p x) (hq'.mul hf')).symm
  ext s hs
  simpa only [lintegral_indicator_one hs] using he (s.indicator 1) (measurable_const.indicator hs)

#print axioms affine_gaussian_density
#print axioms weighted_joint
end Green54GaussianKernel
