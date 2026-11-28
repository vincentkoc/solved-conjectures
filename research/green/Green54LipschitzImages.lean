import Green54GaussianApproximation
import Green54ContractionReduction

/-! Centered finite-dimensional Lipschitz Gaussian images lie in the weak closure
of the laws of finite adapted Gaussian contractions. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal Pointwise
open Green54Contractions Green54GaussianApproximation Green54ContractionReduction Green54Projections
namespace Green54LipschitzImages
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

private theorem scaled_integrable {T : E → E} (hT : LipschitzWith 2 T) (b : ℝ) :
    Integrable (fun z : E => T (b • z)) (stdGaussian E) := by
  have hG := (IsGaussian.memLp_two_id (μ := stdGaussian E)).norm.integrable (by norm_num)
  have hm := hT.continuous.measurable.comp ((measurable_const (a := b)).smul measurable_id)
  apply ((hG.const_mul (2 * ‖b‖)).add (integrable_const ‖T 0‖)).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro z
  have h := hT.norm_sub_le (b • z) 0
  simp only [sub_zero, norm_smul, NNReal.coe_ofNat] at h
  change ‖T (b • z)‖ ≤ 2 * ‖b‖ * ‖z‖ + ‖T 0‖
  linarith [norm_sub_norm_le (T (b • z)) (T 0)]

/-- Rescaling the Gaussian image and its mean by the leave-one-out factor
converges to the centered image at each Gaussian sample. -/
theorem profile_tendsto {T : E → E} (hT : LipschitzWith 2 T) (z : E) :
    Tendsto (fun n => profile T n z) atTop (𝓝 ((2 : ℝ)⁻¹ • (T z - ∫ g, T g ∂stdGaussian E))) := by
  let γ := stdGaussian E
  let b := fun n => (scale n)⁻¹
  have hb : Tendsto b atTop (𝓝 1) := by simpa [b] using scale_tendsto.inv₀ (by norm_num)
  have hG : Integrable (fun g : E => ‖g‖) γ := (IsGaussian.memLp_two_id (μ := γ)).norm.integrable (by norm_num)
  have hT₀ : Integrable T γ := by simpa using scaled_integrable hT 1
  have hdist (n : ℕ) :
      dist (∫ g, T (b n • g) ∂γ) (∫ g, T g ∂γ) ≤ (2 * ‖b n - 1‖) * ∫ g, ‖g‖ ∂γ := by
    rw [dist_eq_norm, ← integral_sub (scaled_integrable hT (b n)) hT₀, ← integral_const_mul]
    apply norm_integral_le_of_norm_le (hG.const_mul _) (ae_of_all _ fun g => ?_)
    have hg : b n • g - g = (b n - 1) • g := by rw [sub_smul, one_smul]
    simpa only [hg, norm_smul, mul_assoc, NNReal.coe_ofNat] using hT.norm_sub_le (b n • g) g
  have hlim : Tendsto (fun n => ∫ g, T (b n • g) ∂γ) atTop (𝓝 (∫ g, T g ∂γ)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) hdist
    simpa using (((tendsto_const_nhds (x := (2 : ℝ))).mul
      ((hb.sub (tendsto_const_nhds (x := (1 : ℝ)))).norm)).mul_const (∫ g, ‖g‖ ∂γ))
  have hz : Tendsto (fun n => T (b n • z)) atTop (𝓝 (T z)) := by
    exact (hT.continuous.tendsto z).comp (by simpa using hb.smul (tendsto_const_nhds (x := z)))
  simpa only [profile, b, γ, one_div] using (scale_tendsto.div_const (2 : ℝ)).smul (hz.sub hlim)

/-- Half of any centered 2-Lipschitz image of the standard Gaussian has a law in
the weak closure of the finite adapted-contraction laws. -/
theorem centered_law_mem_closure {T : E → E} (hT : LipschitzWith 2 T) :
    ∃ ν ∈ closure (adaptedLaws ι), (ν : Measure E) =
      (stdGaussian E).map (fun g => (2 : ℝ)⁻¹ • (T g - ∫ w, T w ∂stdGaussian E)) := by
  classical
  let γ := stdGaussian E
  let Z (z : E) := (2 : ℝ)⁻¹ • (T z - ∫ w, T w ∂γ)
  have hZm : Measurable Z := (measurable_const (a := (2 : ℝ)⁻¹)).smul
    (hT.continuous.measurable.sub measurable_const)
  let X (n : ℕ) := contractedSum (coefficient (n := n) T)
  let ν (n : ℕ) : ProbabilityMeasure E := ⟨(paths ι n).map (X n),
    Measure.isProbabilityMeasure_map (contracted_measurable T).aemeasurable⟩
  let τ : ProbabilityMeasure E := ⟨γ.map Z, Measure.isProbabilityMeasure_map hZm.aemeasurable⟩
  refine ⟨τ, ?_, rfl⟩
  apply isClosed_closure.mem_of_tendsto (f := ν) (b := atTop) _ (Eventually.of_forall fun n =>
    subset_closure (show ν n ∈ adaptedLaws ι from
      ⟨n+1,Nat.succ_pos n,coefficient T,coefficient_measurable T,coefficient_contraction hT,rfl⟩))
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  rintro F ⟨C, hC⟩ ⟨K,hF⟩
  let M := ‖F 0‖ + C
  have hM (v : E) : ‖F v‖ ≤ M := by
    change ‖F v‖ ≤ ‖F 0‖ + C
    linarith [norm_sub_norm_le (F v) (F 0), (show ‖F v - F 0‖ ≤ C by simpa only [dist_eq_norm] using hC v 0)]
  have hFm := hF.continuous.measurable
  have hY : Tendsto (fun n => ∫ z, F (profile T n z) ∂γ) atTop (𝓝 (∫ z, F (Z z) ∂γ)) :=
    tendsto_integral_filter_of_dominated_convergence (fun _ => M)
      (.of_forall fun n => (hFm.comp (profile_measurable hT n)).aestronglyMeasurable)
      (.of_forall fun n => ae_of_all _ fun z => hM _) (integrable_const M)
      (ae_of_all _ fun z => (hF.continuous.tendsto (Z z)).comp (profile_tendsto hT z))
  have hcomp (n : ℕ) : (∫ z, F (profile T n z) ∂γ) =
      ∫ x, F (profile T n (normalizedSum (n+1) x)) ∂paths ι n := by
    have hp := normalizedSum_preserving (ι := ι) (Nat.succ_pos n)
    calc
      _ = ∫ z, F (profile T n z) ∂(paths ι n).map (normalizedSum (n+1)) := by rw [hp.map_eq]
      _ = _ := integral_map hp.measurable.aemeasurable ((hFm.comp (profile_measurable hT n)).aestronglyMeasurable)
  have hdist (n : ℕ) (hn : 0 < n) :
      dist (∫ z, F (profile T n z) ∂γ) (∫ x, F (X n x) ∂paths ι n) ≤
        K * ∫ x, ‖profile T n (normalizedSum (n+1) x) - X n x‖ ∂paths ι n := by
    let Y (x : Fin (n+1) → E) := profile T n (normalizedSum (n+1) x)
    have hmY := (profile_measurable hT n).comp (normalizedSum_preserving (ι := ι) (Nat.succ_pos n)).measurable
    have hYint : Integrable (fun x => F (Y x)) (paths ι n) :=
      Integrable.of_bound (hFm.comp hmY).aestronglyMeasurable M (ae_of_all _ fun x => hM _)
    have hXint : Integrable (fun x => F (X n x)) (paths ι n) :=
      Integrable.of_bound (hFm.comp (contracted_measurable T)).aestronglyMeasurable M (ae_of_all _ fun x => hM _)
    rw [hcomp n, dist_eq_norm, ← integral_sub hYint hXint]
    have he : Integrable (fun x => ‖Y x - X n x‖) (paths ι n) := by
        simp only [Y, X, profile_sub_contracted hn hT, norm_smul]
        exact ((path_error_memLp (n := n) hT).norm.integrable (by norm_num)).const_mul _
    rw [← integral_const_mul]
    exact norm_integral_le_of_norm_le (he.const_mul _) (ae_of_all _ fun x => hF.norm_sub_le _ _)
  change Tendsto (fun n => ∫ z, F z ∂(paths ι n).map (X n)) atTop (𝓝 (∫ z, F z ∂γ.map Z))
  have hpush (n : ℕ) : (∫ z, F z ∂(paths ι n).map (X n)) = ∫ x, F (X n x) ∂paths ι n :=
    integral_map (contracted_measurable T).aemeasurable hFm.aestronglyMeasurable
  simp only [integral_map hZm.aemeasurable hFm.aestronglyMeasurable, hpush]
  apply hY.congr_dist
  exact squeeze_zero' (.of_forall fun _ => dist_nonneg) ((eventually_gt_atTop 0).mono fun n hn => hdist n hn)
    (by simpa [X] using (tendsto_const_nhds (x := (K : ℝ))).mul (mean_coupling_error_tendsto hT))

/-- Every centered 2-Lipschitz image of a standard Gaussian is a sum of two
standard Gaussian vectors with a joint law that may depend on the image. -/
theorem centered_lipschitz_sum {T : E → E} (hT : LipschitzWith 2 T) :
    ∃ ρ : ProbabilityMeasure (E × E),
      (ρ : Measure (E × E)).map Prod.fst = stdGaussian E ∧
      (ρ : Measure (E × E)).map Prod.snd = stdGaussian E ∧
      (ρ : Measure (E × E)).map (fun z => z.1 + z.2) =
        (stdGaussian E).map (fun g => T g - ∫ w, T w ∂stdGaussian E) := by
  classical
  obtain ⟨ν,hν,hmap⟩ := centered_law_mem_closure hT
  obtain ⟨ρ,h₁,h₂,hs⟩ := closure_adaptedLaws_subset hν
  refine ⟨ρ,h₁,h₂,?_⟩
  have hTm := hT.continuous.measurable
  have h := congrArg (Measure.map (fun v : E => (2 : ℝ) • v)) (hs.trans hmap)
  rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)] at h
  simpa [Function.comp_def, smul_smul] using h

/-- The exact Lipschitz approximation input in the Gaussian transport reduction. -/
theorem lipschitzApproximation : LipschitzApproximation := by
  intro J T hT
  obtain ⟨ν,hν,hlaw⟩ := centered_law_mem_closure hT
  refine ⟨ν,hν,hlaw.trans ?_⟩
  let γ := stdGaussian (EuclideanSpace ℝ J)
  have hi : Integrable T γ := by simpa using scaled_integrable hT 1
  have hmean : (∫ w, T w ∂γ) = WithLp.toLp 2 (fun i => ∫ w, T w i ∂γ) := by
    ext i
    exact ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : J => ℝ) i).integral_comp_comm hi).symm
  rw [hmean]

/-- Contractive transport for smooth positive log-concave Gaussian tilts
implies the pinned positive Green 54 statement. -/
theorem green_54_of_contractive_transport (ht : ContractiveTransport) :
    ∀ K : Set (ℕ → ℝ), IsCompact K → Balanced ℝ K → (0.99 : ℝ≥0∞) ≤ gaussian K →
    ∃ C : Set (ℕ → ℝ), IsCompact C ∧ Convex ℝ C ∧ C ⊆ (10 : ℕ) • K ∧
      (0.01 : ℝ≥0∞) ≤ gaussian C :=
  green_54_of_approximation_and_transport lipschitzApproximation ht

#print axioms profile_tendsto
#print axioms centered_law_mem_closure
#print axioms centered_lipschitz_sum
#print axioms lipschitzApproximation
#print axioms green_54_of_contractive_transport

end Green54LipschitzImages
