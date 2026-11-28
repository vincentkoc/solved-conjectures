import ThetaPrimeLaw
import ThetaCharacterCoefficient
import ThetaRowReflection

/-! The symmetric limiting law and two-sided prime excursions of the original theta residual. -/
namespace Arxiv.«2501.03234».ThetaPrimeLaw
open ThetaProfiniteUnits ThetaNaturalPrimeMeans ThetaPeriodMeans ThetaConditionalRows
open Filter MeasureTheory Finset
open scoped Topology NNReal
noncomputable section
local instance (n : ℕ) : NeZero n.factorial := ⟨(Nat.factorial_pos _).ne'⟩

open ThetaCharacterPrimeMeans ThetaPrimeTailTransfer ThetaDivisibleDiagonal ThetaDiagonalConstant

private theorem diagonal_error_mean :
    Tendsto (primeMean (fun p => |residual p-(diagonalConstant+(8/Real.pi^2)*scaledOff p)|))
      atTop (𝓝 0) := by
  apply prime_mean_of_convergence
  intro ε he
  filter_upwards [Metric.tendsto_nhds.mp diagonal_second_order ε he,eventually_gt_atTop 2] with p H hp hprime
  let : Fact p.Prime := ⟨hprime⟩
  have heq : residual p-(diagonalConstant+(8/Real.pi^2)*scaledOff p) =
      divisibleDiagonal p/p - Real.log p/2-diagonalConstant := by
    simp only [ThetaCharacterPrimeMeans.residual,scaledOff,S_eq_diagonal_add_offDiagonal (hprime.eq_two_or_odd.resolve_left (by omega)),add_div]
    field_simp [Real.pi_ne_zero]
    ring
  simpa only [heq,sub_zero,abs_abs, Real.dist_eq] using H

/-- A periodic model lifted from the scaled off-diagonal to the original residual. -/
noncomputable def residualModel (T V p : ℕ) : ℝ := diagonalConstant+(8/Real.pi^2)*model T V p

theorem residualModel_periodic (T V : ℕ) : OnMod T.factorial (residualModel T V) := by
  have hper : OnMod T.factorial (model T V) := low_onMod
    (fun d hd _ => Nat.dvd_factorial (by have := (mem_Icc.mp hd).1; omega) (mem_Icc.mp hd).2) _ _
  intro n
  simp only [residualModel,hper n]

/-- Explicit reciprocal models approximate the original residual in ordinary prime mean. -/
theorem residual_model_approximation {ε : ℝ} (he : 0 < ε) :
    ∃ T V : ℕ, ∀ᶠ X : ℕ in atTop, primeMean (fun p => |residual p-residualModel T V p|) X ≤ ε := by
  let c := 8/Real.pi^2
  have hc : 0<c := by dsimp [c]; positivity
  obtain ⟨T,V,_,_,hv⟩ := prime_model_absolute (show 0 < ε/(2*c) by positivity)
  let g (p : ℕ) := diagonalConstant+c*model T V p
  refine ⟨T,V,?_⟩
  change ∀ᶠ X : ℕ in atTop, primeMean (fun p => |residual p-g p|) X ≤ ε
  have hπ := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp Nat.tendsto_primeCounting
  filter_upwards [hv,diagonal_error_mean.eventually_le_const (half_pos he),hπ.eventually_gt_atTop 0] with X H hdiag hX
  let d (p : ℕ) := diagonalConstant+c*scaledOff p
  have hpoint (p) : |residual p-g p| ≤ |residual p-d p| + c*|scaledOff p-model T V p| := by
    have h := abs_sub_le (residual p) (d p) (g p)
    rw [show d p-g p=c*(scaledOff p-model T V p) by dsimp [d,g]; ring,abs_mul,abs_of_pos hc] at h
    exact h
  have h := mean_mono hpoint X
  rw [mean_add] at h
  have hscale : primeMean (fun p => c*|scaledOff p-model T V p|) X =
      c*primeMean (fun p => |scaledOff p-model T V p|) X := by rw [primeMean,primeMean,← mul_sum,mul_div_assoc]
  have hv' : primeMean (fun p => |scaledOff p-model T V p|) X ≤ ε/(2*c) := (div_le_iff₀ hX).mpr H
  rw [hscale] at h
  have heq : c*(ε/(2*c))=ε/2 := by field_simp
  change primeMean (fun p => |residual p-d p|) X ≤ ε/2 at hdiag
  linarith only [h,hdiag,mul_le_mul_of_nonneg_left hv' hc.le,heq]

theorem residual_approximable : Approximable residual := by
  intro ε he
  obtain ⟨T,V,H⟩ := residual_model_approximation he
  exact ⟨T,residualModel T V,residualModel_periodic T V,H⟩

open ThetaCharacterCoefficient ThetaCharacterThree

/-- Even the best point mass is separated from the limiting law by the
exact modulo-three bias in mean absolute distance. -/
theorem law_absolute_spread (hAP : ProgressionMangoldt) {F : G →₁[haar] ℝ}
    (hF : Represents residual F) (t : ℝ) :
    characterConstant ≤ ∫ x, |x-t| ∂(haarLaw F) := by
  have hg : Tendsto (primeMean (fun p => (chi p:ℝ)*(residual p-t))) atTop (𝓝 characterConstant) := by
    have h := (prime_character_exact hAP).sub ((chi_prime_mean hAP).mul_const t)
    simp only [zero_mul,sub_zero] at h
    apply h.congr'
    apply Eventually.of_forall
    intro X
    simp only [primeMean,mul_sub,sum_sub_distrib,← sum_mul]
    ring
  have htest : LipschitzWith 1 (fun x : ℝ => |x-t|) := LipschitzWith.dist_left t
  rw [haarLaw_integral F htest.continuous]
  apply le_of_tendsto_of_tendsto' hg (prime_mean_lipschitz hAP hF htest)
  intro X
  apply mean_mono
  intro p
  have H : |(chi p:ℝ)| ≤ 1 := by unfold chi; split_ifs <;> norm_num
  exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) H)

theorem law_nonconstant (hAP : ProgressionMangoldt) {F : G →₁[haar] ℝ}
    (hF : Represents residual F) (t : ℝ) : (haarLaw F : Measure ℝ) ≠ Measure.dirac t := by
  intro he
  have hs := law_absolute_spread hAP hF t
  rw [he,integral_dirac] at hs
  simp only [sub_self,abs_zero] at hs
  obtain ⟨C,hC,hc,_⟩ := S_class_prime_means hAP
  have H := tendsto_nhds_unique hc (prime_character_exact hAP)
  linarith only [hs,hC,H,show 0 < (968:ℝ)/(375*Real.pi^2) by positivity]

open ThetaPrimeDensity

theorem empirical_real_set {X : ℕ} (hX : 2 ≤ X) (f : ℕ → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    (empirical f X : Measure ℝ).real s = (primeSet (fun p => f p∈s) X).card / (X.primeCounting:ℝ) := by
  classical
  rw [← integral_indicator_one hs,empirical_integral hX f (measurable_one.indicator hs)]
  simp only [primeMean,primeSet,Set.indicator_apply,Pi.one_apply,sum_boole]

theorem mass_lower_of_count {f : ℕ → ℝ} {μ : ProbabilityMeasure ℝ} {P : ℕ → Prop}
    {s : Set ℝ} (hs : IsClosed s) (hc : Tendsto (empirical f) atTop (𝓝 μ))
    {δ : ℝ} (h : ∀ᶠ X in atTop,δ*X.primeCounting ≤ ((primeSet P X).card:ℝ)) (hsub : ∀ p, p.Prime → P p → f p ∈ s) :
    ENNReal.ofReal δ ≤ (μ : Measure ℝ) s := by
  classical
  have hπ := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp Nat.tendsto_primeCounting
  have he : ∀ᶠ X : ℕ in atTop, ENNReal.ofReal δ ≤ (empirical f X : Measure ℝ) s := by
    filter_upwards [h,eventually_ge_atTop 2,hπ.eventually_gt_atTop 0] with X hX hx hp
    apply ENNReal.ofReal_le_of_le_toReal
    change δ ≤ (empirical f X : Measure ℝ).real s
    rw [empirical_real_set hx f hs.measurableSet]
    apply (le_div_iff₀ hp).mpr
    apply hX.trans
    exact_mod_cast card_le_card (show primeSet P X ⊆ primeSet (fun p => f p ∈ s) X by
      intro p h
      obtain ⟨h,h'⟩ := mem_filter.mp h
      exact mem_filter.mpr ⟨h,hsub p (Nat.prime_of_mem_primesLE h) h'⟩)
  exact (le_limsup_of_frequently_le he.frequently).trans (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hc hs)

theorem positive_mass_of_density {f : ℕ → ℝ} {μ : ProbabilityMeasure ℝ} {P : ℕ → Prop}
    {s : Set ℝ} (hs : IsClosed s) (hc : Tendsto (empirical f) atTop (𝓝 μ))
    (hP : PositiveLowerPrimeDensity P) (hsub : ∀ p, p.Prime → P p → f p ∈ s) :
    0 < (μ : Measure ℝ) s := by
  obtain ⟨δ,hδ,h⟩ := hP
  exact (ENNReal.ofReal_pos.mpr hδ).trans_le (mass_lower_of_count hs hc h hsub)

/-- The limiting distribution assigns positive probability to both separated
closed half-lines detected by the original signed prime excursions. -/
theorem law_two_tails (hAP : ProgressionMangoldt) {F : G →₁[haar] ℝ} (hF : Represents residual F) :
    0 < (haarLaw F : Measure ℝ) (Set.Ici (13/50:ℝ)) ∧
    0 < (haarLaw F : Measure ℝ) (Set.Iic (-(1/1000):ℝ)) := by
  have h := empirical_tendsto hAP hF
  obtain ⟨hpos,hneg⟩ := S_half_log_lower_densities hAP
  constructor
  · apply positive_mass_of_density isClosed_Ici h hpos
    intro p hp hh
    have hp' : (0:ℝ)<p := by exact_mod_cast hp.pos
    change 13/50 ≤ (S p:ℝ)/p-Real.log p/2
    apply sub_nonneg.mp
    rw [sub_sub, sub_nonneg,le_div_iff₀ hp']
    nlinarith only [hh.2]
  · apply positive_mass_of_density isClosed_Iic h hneg
    intro p hp hh
    have hp' : (0:ℝ)<p := by exact_mod_cast hp.pos
    change (S p:ℝ)/p-Real.log p/2 ≤ -(1/1000)
    rw [sub_le_iff_le_add,div_le_iff₀ hp']
    nlinarith only [hh.2]

private lemma reflected_test {φ : ℝ → ℝ} {K : ℝ≥0} (hp : LipschitzWith K φ) (B : ℝ) :
    LipschitzWith K (fun x => φ (2*B-x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq,sub_sub_sub_cancel_left,abs_sub_comm y x] using hp.dist_le_mul (2*B-x) (2*B-y)

private theorem symmetric_integral (hAP : ProgressionMangoldt) {F : ThetaProfiniteUnits.G →₁[ThetaProfiniteUnits.haar] ℝ}
    (hF : Represents residual F) {φ : ℝ → ℝ} {K : ℝ≥0} (hp : LipschitzWith K φ) :
    (∫ x, φ x ∂(haarLaw F)) = ∫ x, φ (2*diagonalConstant-x) ∂(haarLaw F) := by
  let ψ (x : ℝ) := φ (2*diagonalConstant-x)
  have hψ := reflected_test hp diagonalConstant
  have hA := prime_mean_lipschitz hAP hF hp
  have hB := prime_mean_lipschitz hAP hF hψ
  rw [← haarLaw_integral F hp.continuous] at hA
  rw [← haarLaw_integral F hψ.continuous] at hB
  apply eq_of_abs_sub_le_all
  intro ε he
  let η := ε/(2*(K:ℝ)+2)
  have hη : 0<η := by dsimp [η]; positivity
  obtain ⟨T,V,he'⟩ := residual_model_approximation hη
  let g := residualModel T V
  have hg := residualModel_periodic T V
  have hmφ := periodic_prime_mean hAP (show OnMod T.factorial (fun p => φ (g p)) from fun n => congrArg φ (hg n))
  have hmψ := periodic_prime_mean hAP (show OnMod T.factorial (fun p => ψ (g p)) from fun n => congrArg ψ (hg n))
  have H : unitMean T.factorial (fun p => φ (g p)) = unitMean T.factorial (fun p => ψ (g p)) := by
    dsimp only [ψ,g,residualModel]
    simp only [show ∀ x c : ℝ, 2*diagonalConstant-(diagonalConstant+c*x)=diagonalConstant-c*x by intros; ring]
    exact ThetaRowReflection.finite_test_reflection ..
  have H₁ := hA.sub hmφ
  have H₂ := hB.sub hmψ
  have H₁' := le_of_tendsto H₁.abs (he'.mono (fun X h => (lipschitz_mean hp residual g X).trans
    (mul_le_mul_of_nonneg_left h K.2)))
  have H₂' := le_of_tendsto H₂.abs (he'.mono (fun X h => (lipschitz_mean hψ residual g X).trans
    (mul_le_mul_of_nonneg_left h K.2)))
  rw [H] at H₁'
  have hcan : (2*(K:ℝ)+2)*η=ε := by dsimp [η]; field_simp
  apply abs_le.mpr
  obtain ⟨hl₁,hu₁⟩ := abs_le.mp H₁'
  obtain ⟨hl₂,hu₂⟩ := abs_le.mp H₂'
  dsimp only [ψ] at *
  constructor <;> linarith
/-- Push a law forward by reflection about B. -/
def reflectedLaw (B : ℝ) (μ : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  μ.map (f:=fun x : ℝ => 2*B-x) (by fun_prop)

/-- Reflection about the all-prime mean preserves the entire limiting law. -/
theorem law_symmetric (hAP : ProgressionMangoldt) {F : ThetaProfiniteUnits.G →₁[ThetaProfiniteUnits.haar] ℝ}
    (hF : Represents residual F) :
    reflectedLaw diagonalConstant (haarLaw F) = haarLaw F := by
  let r (x : ℝ) := 2*diagonalConstant-x
  have hr : Continuous r := continuous_const.sub continuous_id
  let ν := (haarLaw F).map (f:=r) hr.aemeasurable
  have H : Tendsto (fun _ : ℕ => ν) atTop (𝓝 (haarLaw F)) := by
    apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
    intro φ _ ⟨K,hp⟩
    have heq : (∫ x, φ x ∂ν) = ∫ x, φ x ∂(haarLaw F) := by
      change (∫ x, φ x ∂((haarLaw F : Measure ℝ).map r)) = _
      rw [integral_map hr.aemeasurable hp.continuous.aestronglyMeasurable]
      exact (symmetric_integral hAP hF hp).symm
    simpa only [heq] using (tendsto_const_nhds (x:=(∫ x, φ x ∂ν)) (f:=atTop (α:=ℕ)))
  exact tendsto_nhds_unique tendsto_const_nhds H

#print axioms law_symmetric

/-- The residual of the original integer theta sum has a common profinite
Haar representative. Its empirical laws converge weakly, its Lipschitz
means converge, and the law charges both specified half-lines. -/
theorem S_prime_residual_distribution (hAP : ProgressionMangoldt) :
    ∃ F : G →₁[haar] ℝ, Represents residual F ∧
      reflectedLaw diagonalConstant (haarLaw F) = haarLaw F ∧
      Tendsto (empirical residual) atTop (𝓝 (haarLaw F)) ∧
      (∀ (φ : ℝ → ℝ) (K : ℝ≥0), LipschitzWith K φ →
        Tendsto (primeMean (fun p => φ (residual p))) atTop (𝓝 (∫ x, φ x ∂(haarLaw F)))) ∧
      (∫ x, x ∂(haarLaw F)) = diagonalConstant ∧
      (∀ t : ℝ, characterConstant ≤ ∫ x, |x-t| ∂(haarLaw F)) ∧
      (∀ t : ℝ, (haarLaw F : Measure ℝ) ≠ Measure.dirac t) ∧
      0 < (haarLaw F : Measure ℝ) (Set.Ici (13/50:ℝ)) ∧
      0 < (haarLaw F : Measure ℝ) (Set.Iic (-(1/1000):ℝ)) := by
  obtain ⟨F,hr⟩ := exists_haar_representative hAP residual_approximable
  have ht (φ : ℝ → ℝ) (K : ℝ≥0) (hφ : LipschitzWith K φ) :
      Tendsto (primeMean (fun p => φ (residual p))) atTop (𝓝 (∫ x, φ x ∂(haarLaw F))) := by
    rw [haarLaw_integral F hφ.continuous]
    exact prime_mean_lipschitz hAP hr hφ
  refine ⟨F,hr,law_symmetric hAP hr,empirical_tendsto hAP hr,ht,?_,law_absolute_spread hAP hr,
    law_nonconstant hAP hr,law_two_tails hAP hr⟩
  exact tendsto_nhds_unique (ht id 1 LipschitzWith.id) (S_second_order_prime_mean hAP)

#print axioms S_prime_residual_distribution

#print axioms residual_approximable
#print axioms law_absolute_spread
#print axioms law_nonconstant
#print axioms law_two_tails

private lemma mass_reflected (B t : ℝ) (μ : ProbabilityMeasure ℝ) (h : reflectedLaw B μ = μ) :
    (μ : Measure ℝ) (Set.Ioi (B+t)) = (μ : Measure ℝ) (Set.Iio (B-t)) := by
  calc
    _ = (reflectedLaw B μ : Measure ℝ) (Set.Ioi (B+t)) := by rw [h]
    _ = (μ : Measure ℝ) ((fun x : ℝ => 2*B-x) ⁻¹' Set.Ioi (B+t)) := by
      change (Measure.map (fun x : ℝ => 2*B-x) (μ:Measure ℝ)) _ = _
      apply Measure.map_apply (by fun_prop) measurableSet_Ioi
    _ = _ := by congr 1; ext x; simp only [Set.mem_preimage,Set.mem_Ioi,Set.mem_Iio]; constructor <;> intro h <;> linarith

private lemma mass_beyond (hAP : ProgressionMangoldt) {F : G →₁[haar] ℝ} (hF : Represents residual F)
    {t : ℝ} (ht : t < characterConstant) :
    0 < (haarLaw F : Measure ℝ) (Set.Ioi (diagonalConstant+t)) ∧
      0 < (haarLaw F : Measure ℝ) (Set.Iio (diagonalConstant-t)) := by
  let μ := haarLaw F
  have heq := mass_reflected diagonalConstant t μ (law_symmetric hAP hF)
  suffices 0 < (μ : Measure ℝ) (Set.Ioi (diagonalConstant+t)) from ⟨this,heq ▸ this⟩
  by_contra! hz
  have hz' := le_antisymm hz bot_le
  have hzero : (μ:Measure ℝ) (Set.Iio (diagonalConstant-t)) = 0 := heq ▸ hz'
  have hhi : ∀ᵐ x ∂(μ:Measure ℝ), x ≤ diagonalConstant+t := by simpa only [ae_iff,not_le,Set.Ioi] using hz'
  have hlo : ∀ᵐ x ∂(μ:Measure ℝ), diagonalConstant-t ≤ x := by simpa only [ae_iff,not_le,Set.Iio] using hzero
  have hi : Integrable (fun x : ℝ => |x-diagonalConstant|) (μ:Measure ℝ) := by
    change Integrable _ (Measure.map (fun x => F x) haar)
    apply (integrable_map_measure (by fun_prop) (Lp.aestronglyMeasurable F).aemeasurable).mpr
    exact ((L1.integrable_coeFn F).sub (integrable_const _)).abs
  have hu : (∫ x, |x-diagonalConstant| ∂(μ:Measure ℝ)) ≤ t := by
    calc
      _ ≤ ∫ _ : ℝ, t ∂(μ:Measure ℝ) := by
        apply integral_mono_ae hi (integrable_const _)
        filter_upwards [hhi,hlo] with x hx hy
        exact abs_le.mpr ⟨by linarith,by linarith⟩
      _ = t := by simp
  exact ht.not_ge ((law_absolute_spread hAP hF diagonalConstant).trans hu)

private lemma density_of_open_mass {f : ℕ → ℝ} {μ : ProbabilityMeasure ℝ} {s : Set ℝ}
    (hs : IsOpen s) (hc : Tendsto (empirical f) atTop (𝓝 μ)) (hm : 0 < (μ : Measure ℝ) s) :
    PositiveLowerPrimeDensity (fun p => f p ∈ s) := by
  let m := (μ:Measure ℝ).real s
  have hfin : (μ:Measure ℝ) s ≠ ⊤ := measure_ne_top _ _
  have hm' : 0 < m := ENNReal.toReal_pos hm.ne' hfin
  have hlt : ENNReal.ofReal (m/2) < (μ:Measure ℝ) s :=
    (ENNReal.ofReal_lt_iff_lt_toReal (half_pos hm').le hfin).mpr (half_lt_self hm')
  have H := eventually_lt_of_lt_liminf (hlt.trans_le
    (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hc hs))
  refine ⟨m/2,half_pos hm',?_⟩
  have hπ := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp Nat.tendsto_primeCounting
  filter_upwards [H,eventually_ge_atTop 2,hπ.eventually_gt_atTop 0] with X h hx hp
  have hv := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp h.le
  change m/2 ≤ (empirical f X : Measure ℝ).real s at hv
  rw [empirical_real_set hx f hs.measurableSet] at hv
  exact (le_div_iff₀ hp).mp hv

/-- Every threshold below the exact modulo-three bias gives two symmetric
excursions about the mean on positive lower fractions of the primes. -/
theorem S_prime_reflected_excursions (hAP : ProgressionMangoldt) {t : ℝ} (ht : t < characterConstant) :
    PositiveLowerPrimeDensity (fun p => diagonalConstant+t < residual p) ∧
      PositiveLowerPrimeDensity (fun p => residual p < diagonalConstant-t) := by
  obtain ⟨F,hF⟩ := exists_haar_representative hAP residual_approximable
  have h := empirical_tendsto hAP hF
  obtain ⟨hp,hn⟩ := mass_beyond hAP hF ht
  have hi := density_of_open_mass (f:=ThetaCharacterPrimeMeans.residual) (μ:=haarLaw F)
    (s:=Set.Ioi (diagonalConstant+t)) isOpen_Ioi h hp
  have lo := density_of_open_mass (f:=ThetaCharacterPrimeMeans.residual) (μ:=haarLaw F)
    (s:=Set.Iio (diagonalConstant-t)) isOpen_Iio h hn
  exact ⟨hi,lo⟩

#print axioms S_prime_reflected_excursions

end
end Arxiv.«2501.03234».ThetaPrimeLaw
