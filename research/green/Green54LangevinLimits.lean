import Green54LangevinPaths

/-! Closedness of two-Gaussian sum laws under centered Langevin approximation. -/
open MeasureTheory ProbabilityTheory Set
open scoped NNReal RealInnerProductSpace Topology
noncomputable section
namespace Green54LangevinLimits
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
omit [BorelSpace E] [SecondCountableTopology E] in
/-- A uniform Lipschitz-test bound controls the norm of the difference of the means. -/
theorem mean_distance {μ ν : Measure E} (hμ : Integrable (id : E → E) μ) (hν : Integrable (id : E → E) ν)
    {ε : ℝ} (hε : 0 ≤ ε) (he : ∀ {K : NNReal} {f : E → ℝ}, LipschitzWith K f →
      |(∫ x, f x ∂μ)-(∫ x, f x ∂ν)| ≤ (K:ℝ)*ε) :
    ‖(∫ x, x ∂μ)-(∫ x, x ∂ν)‖ ≤ ε := by
  let v := (∫ x, x ∂μ)-(∫ x, x ∂ν)
  have hl : LipschitzWith ‖v‖₊ (fun x : E => ⟪v,x⟫) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm,←inner_sub_right, Real.norm_eq_abs,coe_nnnorm] using abs_real_inner_le_norm v (x-y)
  have h := he hl
  change Integrable (fun x : E => x) μ at hμ
  change Integrable (fun x : E => x) ν at hν
  rw [integral_inner hμ,integral_inner hν,← inner_sub_right] at h
  change |⟪v,v⟫| ≤ ‖v‖*ε at h
  rw [real_inner_self_eq_norm_sq,abs_of_nonneg (sq_nonneg _)] at h
  by_cases hv : ‖v‖ = 0
  · change ‖v‖ ≤ ε
    simpa [hv] using hε
  · change ‖v‖ ≤ ε
    nlinarith [lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)]
omit [SecondCountableTopology E] in
private theorem centered_test {μ ν : Measure E} [IsProbabilityMeasure μ]
    (hμ : Integrable (id : E → E) μ) (hν : Integrable (id : E → E) ν)
    {ε : ℝ} (hε : 0 ≤ ε) (he : ∀ {K : NNReal} {f : E → ℝ}, LipschitzWith K f →
      |(∫ x, f x ∂μ)-(∫ x, f x ∂ν)| ≤ (K:ℝ)*ε)
    {K : NNReal} {F : E → ℝ} (hF : LipschitzWith K F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C) :
    |(∫ x, F (x-∫ y, y ∂μ) ∂μ)-(∫ x, F (x-∫ y, y ∂ν) ∂ν)| ≤ 2*(K:ℝ)*ε := by
  let m := ∫ y, y ∂μ
  let t := ∫ y, y ∂ν
  let g (v x : E) := F (x-v)
  have hl (v : E) : LipschitzWith K (g v) := LipschitzWith.of_dist_le_mul fun x y => by
    simpa only [g,dist_sub_right] using hF.dist_le_mul (x-v) (y-v)
  have hi (v : E) : Integrable (g v) μ :=
    Integrable.of_bound (hl v).continuous.aestronglyMeasurable C (ae_of_all _ fun _ => hC _)
  have hd := mean_distance hμ hν hε he
  have h₁ : |(∫ x, g m x ∂μ)-(∫ x, g t x ∂μ)| ≤ (K:ℝ)*ε := by
    rw [← integral_sub (hi m) (hi t),←Real.norm_eq_abs]
    have hb (x : E) : ‖g m x-g t x‖ ≤ (K:ℝ)*ε := by
      have h := hF.norm_sub_le (x-m) (x-t)
      rw [show (x-m)-(x-t)= -(m-t) by abel,norm_neg] at h
      exact h.trans (mul_le_mul_of_nonneg_left hd K.coe_nonneg)
    simpa using norm_integral_le_of_norm_le (integrable_const (μ := μ) ((K:ℝ)*ε)) (ae_of_all _ hb)
  have h₂ := he (hl t)
  have ht := abs_sub_le (∫ x, g m x ∂μ) (∫ x, g t x ∂μ) (∫ x, g t x ∂ν)
  change |(∫ x, g m x ∂μ)-(∫ x, g t x ∂ν)| ≤ _
  linarith

open Green54Contractions Filter
open scoped Topology
/-- Probability laws of sums with the same prescribed law on both coordinates. -/
def sumLaws (γ : Measure E) : Set (ProbabilityMeasure E) :=
  {μ | ∃ ρ : ProbabilityMeasure (E × E), (ρ : Measure (E × E)).map Prod.fst = γ ∧
    (ρ : Measure (E × E)).map Prod.snd = γ ∧ (ρ : Measure (E × E)).map (fun z => z.1+z.2) = (μ : Measure E)}

theorem compact_sum_laws (γ : Measure E) [IsProbabilityMeasure γ] : IsCompact (sumLaws γ) := by
  let half (x : E) := (2:ℝ)⁻¹ • x
  let twice (x : E) := (2:ℝ) • x
  have hh : Continuous half := by unfold half; fun_prop
  have ht : Continuous twice := by unfold twice; fun_prop
  convert (isCompact_midpointLaws γ).image (ProbabilityMeasure.continuous_map ht) using 1
  ext ν
  constructor
  · rintro ⟨ρ,h₁,h₂,hρ⟩
    refine ⟨ν.map hh.measurable.aemeasurable,⟨ρ,h₁,h₂,?_⟩,?_⟩
    · change _ = (ν : Measure E).map half
      rw [← hρ, Measure.map_map hh.measurable (by fun_prop)]
      rfl
    · apply ProbabilityMeasure.toMeasure_injective
      change ((ν : Measure E).map half).map twice = _
      rw [Measure.map_map ht.measurable hh.measurable]
      simp [half,twice,Function.comp_def,smul_smul]
  · rintro ⟨τ,⟨ρ,h₁,h₂,he⟩,rfl⟩
    refine ⟨ρ,h₁,h₂,?_⟩
    change _ = (τ : Measure E).map twice
    rw [← he,Measure.map_map ht.measurable (by fun_prop)]
    simp [twice,Function.comp_def,smul_smul]

def centered (μ : ProbabilityMeasure E) : ProbabilityMeasure E :=
  μ.map (f := fun x => x-∫ y, y ∂(μ : Measure E)) (by fun_prop)

omit [SecondCountableTopology E] in
theorem centered_limit {τ : ProbabilityMeasure E} {μ : ℕ → ProbabilityMeasure E}
    (hτ : Integrable (id : E → E) (τ : Measure E)) (hμ : ∀ n, Integrable (id : E → E) (μ n : Measure E))
    {δ : ℕ → ℝ} (hδ : ∀ n, 0 ≤ δ n) (hlim : Tendsto δ atTop (𝓝 0))
    (he : ∀ n {K : NNReal} {f : E → ℝ}, LipschitzWith K f →
      |(∫ x, f x ∂(μ n : Measure E))-(∫ x, f x ∂(τ : Measure E))| ≤ (K:ℝ)*δ n) :
    Tendsto (fun n => centered (μ n)) atTop (𝓝 (centered τ)) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  rintro F ⟨C,hb⟩ ⟨K,hF⟩
  have hC (x : E) : ‖F x‖ ≤ ‖F 0‖+C := by
    linarith [norm_sub_norm_le (F x) (F 0),show ‖F x-F 0‖ ≤ C by simpa only [dist_eq_norm] using hb x 0]
  have hp (ν : ProbabilityMeasure E) : (∫ x, F x ∂(centered ν : Measure E)) =
      ∫ x, F (x-∫ y, y ∂(ν : Measure E)) ∂(ν : Measure E) :=
    integral_map (by fun_prop) hF.continuous.aestronglyMeasurable
  simpa only [hp] using (show Tendsto (fun n => ∫ x, F (x-∫ y, y ∂(μ n : Measure E)) ∂(μ n : Measure E))
    atTop (𝓝 (∫ x, F (x-∫ y, y ∂(τ : Measure E)) ∂(τ : Measure E))) from by
      apply tendsto_iff_dist_tendsto_zero.mpr
      apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
        (by simpa using hlim.const_mul (2*(K:ℝ)))
      exact centered_test (hμ n) hτ (hδ n) (he n) hF hC)

section Euler
open Green54GaussianIterations Green54LangevinStationarity Green54LangevinPaths
variable {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ ι

private theorem approximate_by_sum {U : V → ℝ} (hU : Measurable U) {G : V → V} {L : NNReal}
    (hG : LipschitzWith L G) (hsub : ∀ x y, ⟪G x,y-x⟫ ≤ U y-U x)
    (hmon : ∀ x y, ‖x-y‖^2 ≤ ⟪x-y,G x-G y⟫) {c : ℝ} (hc : 0 < c)
    (τ : ProbabilityMeasure V)
    (hπ : (τ : Measure V) = volume.withDensity (fun x => ENNReal.ofReal (c*Real.exp (-U x))))
    (h₀ : Integrable (id : V → V) (τ : Measure V))
    (hM : Integrable (fun s : V × V => (‖G s.1‖+2*‖s.2‖)^3) ((τ : Measure V).prod (stdGaussian V)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : ProbabilityMeasure V, Integrable (id : V → V) (μ : Measure V) ∧
      centered μ ∈ sumLaws (stdGaussian V) ∧ ∀ {K : NNReal} {f : V → ℝ}, LipschitzWith K f →
        |(∫ x, f x ∂(μ : Measure V))-(∫ x, f x ∂(τ : Measure V))| ≤ (K:ℝ)*ε := by
  have hn : Integrable (dist (0:V)) (τ : Measure V) := by
    change Integrable (fun x : V => dist 0 x) (τ : Measure V)
    simpa only [dist_zero_left,id_eq] using h₀.norm
  obtain ⟨h,hh,hs,hgrad,n,ha⟩ := approximate_target hU hG hsub hmon hc hπ hM 0 hn hε
  let D (x : V) := x-h • G x
  let r : NNReal := ⟨Real.sqrt (1-h),Real.sqrt_nonneg _⟩
  let σ := Real.sqrt (2*h)
  have hr : (r:ℝ)^2 = 1-h := Real.sq_sqrt (by linarith)
  have hD : LipschitzWith r D := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm,dist_eq_norm]
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg r.coe_nonneg (norm_nonneg _))).mp
    rw [mul_pow,hr]
    exact (gradient_step_sq hG hmon hh.le x y).trans
      (mul_le_mul_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left hgrad hh.le]) (sq_nonneg _))
  have hσ : 0 ≤ σ := Real.sqrt_nonneg _
  have hc' : (r:ℝ)^2+σ^2/4 ≤ 1 := by rw [hr,show σ^2=2*h from Real.sq_sqrt (by positivity)]; linarith
  let T (z : EuclideanSpace ℝ (Fin n × ι)) := chain D σ 0 n (block z)
  have hT : LipschitzWith 2 T := chain_lipschitz hσ (fun x y => hD.norm_sub_le x y) hc' 0 n
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n × ι))
  let μ : ProbabilityMeasure V := ⟨γ.map T, Measure.isProbabilityMeasure_map hT.continuous.measurable.aemeasurable⟩
  have hi : Integrable T γ := by
    have hi := (IsGaussian.memLp_two_id (μ := γ)).norm.integrable (by norm_num)
    apply ((hi.const_mul 2).add (integrable_const ‖T 0‖)).mono' hT.continuous.aestronglyMeasurable
    apply ae_of_all
    intro z
    have hl := hT.norm_sub_le z 0
    simp only [sub_zero,NNReal.coe_ofNat] at hl
    change ‖T z‖ ≤ 2*‖z‖+‖T 0‖
    linarith [norm_sub_norm_le (T z) (T 0)]
  refine ⟨μ,(integrable_map_measure aestronglyMeasurable_id hT.continuous.measurable.aemeasurable).mpr hi,?_,?_⟩
  · obtain ⟨ρ,h₁,h₂,hρ⟩ := Green54RectangularImages.rectangular_sum hT
    refine ⟨ρ,h₁,h₂,hρ.trans ?_⟩
    change γ.map _ = (γ.map T).map (fun x => x-∫ y, y ∂γ.map T)
    have hmean : (∫ y : V, y ∂γ.map T) = ∫ z, T z ∂γ :=
      integral_map hT.continuous.measurable.aemeasurable (f := fun y : V => y) aestronglyMeasurable_id
    rw [hmean,
      Measure.map_map (by fun_prop) hT.continuous.measurable]
    rfl
  · intro K f hf
    change |(∫ x, f x ∂γ.map T)-(∫ x, f x ∂(τ : Measure V))| ≤ _
    rw [integral_map hT.continuous.measurable.aemeasurable hf.continuous.aestronglyMeasurable]
    have he : (∫ x, f (T x) ∂γ) = (transition D σ)^[n] f 0 :=
      gaussian_chain_integral hD hσ hc' 0 n hf
    rw [he]
    exact ha hf

/-- The centered law of a finite-dimensional strongly log-concave target with globally
Lipschitz subgradient and the stated finite moments is a sum of two standard Gaussians. -/
theorem strongly_convex_sum {U : V → ℝ} (hU : Measurable U) {G : V → V} {L : NNReal}
    (hG : LipschitzWith L G) (hsub : ∀ x y, ⟪G x,y-x⟫ ≤ U y-U x)
    (hmon : ∀ x y, ‖x-y‖^2 ≤ ⟪x-y,G x-G y⟫) {c : ℝ} (hc : 0 < c)
    (τ : ProbabilityMeasure V)
    (hπ : (τ : Measure V) = volume.withDensity (fun x => ENNReal.ofReal (c*Real.exp (-U x))))
    (h₀ : Integrable (id : V → V) (τ : Measure V))
    (hM : Integrable (fun s : V × V => (‖G s.1‖+2*‖s.2‖)^3) ((τ : Measure V).prod (stdGaussian V))) :
    centered τ ∈ sumLaws (stdGaussian V) := by
  let δ (n : ℕ) := 1/((n:ℝ)+1)
  have hd (n : ℕ) : 0 < δ n := by unfold δ; positivity
  choose μ hi hμ he using (fun n : ℕ => approximate_by_sum hU hG hsub hmon hc τ hπ h₀ hM (hd n))
  exact (compact_sum_laws (stdGaussian V)).isClosed.mem_of_tendsto
    (centered_limit h₀ hi (fun n => (hd n).le) tendsto_one_div_add_atTop_nhds_zero_nat he)
    (.of_forall hμ)
end Euler

#print axioms mean_distance
#print axioms compact_sum_laws
#print axioms centered_limit
#print axioms strongly_convex_sum
end Green54LangevinLimits
