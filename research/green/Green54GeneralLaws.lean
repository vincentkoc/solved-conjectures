import Green54Solved

/-! Three-Gaussian representations of laws with unbounded support. -/

open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace Green54GeneralLaws
open Green54ConvexTests Green54FiniteLaws

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

/-- Convex order transfers integrability of every continuous convex test. -/
theorem integrable_test {ν γ : Measure E} [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
    (h : ConvexDominated ν γ) {f : C(E, ℝ)} (hf : ConvexOn ℝ univ f) (hi : Integrable f γ) :
    Integrable f ν := by
  by_contra hn
  let c := -(∫ x, f x ∂γ) - 1
  let g : C(E, ℝ) := f + ContinuousMap.const E c
  have hj : Integrable g γ := hi.add (integrable_const c)
  have hle := h g (hf.add_const c) hj
  have hng : ¬ Integrable g ν := by
    intro hg
    apply hn
    have hs : Integrable (fun x => (f x + c) - c) ν := hg.sub (integrable_const c)
    simpa using hs
  rw [integral_undef hng] at hle
  change (0 : ℝ) ≤ ∫ x, f x + c ∂γ at hle
  rw [integral_add hi (integrable_const c), integral_const, probReal_univ, one_smul] at hle
  dsimp [c] at hle
  linarith

#print axioms integrable_test

variable [BorelSpace E] [CompleteSpace E]

/-- Replace the tail outside a compact set by its conditional barycentre. The result
has compact support and remains below the original law in convex order. -/
private theorem truncate_barycentre (ν : ProbabilityMeasure E) {B : Set E} (hcompact : IsCompact B)
    (hi : Integrable id (ν : Measure E)) :
    ∃ (Q : E → E) (_hm : Measurable Q) (K : Set E), IsCompact K ∧ range Q ⊆ K ∧
      (∀ x ∈ B, Q x = x) ∧
      ∀ f : C(E, ℝ), ConvexOn ℝ univ f → Integrable f (ν : Measure E) →
        (∫ x, f (Q x) ∂(ν : Measure E)) ≤ ∫ x, f x ∂(ν : Measure E) := by
  classical
  have hB : MeasurableSet B := hcompact.measurableSet
  let b : E := ⨍ x in Bᶜ, x ∂(ν : Measure E)
  let Q := B.piecewise id (fun _ => b)
  have hm : Measurable Q := measurable_id.piecewise hB measurable_const
  have hon (x : E) (hx : x ∈ B) : Q x = x := by simp [Q,hx]
  have hout (x : E) (hx : x ∈ Bᶜ) : Q x = b := by simp [Q,show x ∉ B from hx]
  refine ⟨Q,hm,B ∪ {b},hcompact.union isCompact_singleton,?_,?_,?_⟩
  · rintro _ ⟨x,rfl⟩
    by_cases hx : x ∈ B
    · exact Or.inl (by rwa [hon x hx])
    · exact Or.inr (mem_singleton_iff.mpr (hout x hx))
  · exact hon
  intro f hf hfi
  have hintegral : Integrable (fun x => f (Q x)) (ν : Measure E) := by
    have hp := Integrable.piecewise hB hfi.integrableOn (integrable_const (f b)).integrableOn
    apply hp.congr
    filter_upwards with x
    by_cases hx : x ∈ B <;> simp [Q,hx]
  rw [← integral_add_compl hB hintegral, ← integral_add_compl hB hfi]
  apply add_le_add
  · exact (setIntegral_congr_fun hB fun x hx => congrArg f (hon x hx)).le
  · rw [setIntegral_congr_fun hB.compl (fun x hx => congrArg f (hout x hx)), setIntegral_const]
    by_cases hz : (ν : Measure E) Bᶜ = 0
    · simp [measureReal_def,hz,Measure.restrict_eq_zero.mpr hz]
    have hj := hf.map_set_average_le f.continuous.continuousOn isClosed_univ hz
      (measure_ne_top _ _) (ae_of_all _ (fun _ => mem_univ _)) hi.integrableOn hfi.integrableOn
    exact (smul_le_smul_of_nonneg_left hj measureReal_nonneg).trans_eq
      (measure_smul_setAverage (μ := (ν : Measure E)) f (measure_ne_top _ _))

variable [SecondCountableTopology E]

/-- Compact support can be removed from a three-marginal decomposition whenever the
reference law has a finite first moment on a separable Banach space. -/
theorem triple_of_compact (γ : Measure E) [IsProbabilityMeasure γ]
    (hγ : Integrable id γ) (ht : CompactTripleDecomposition γ) (ν : ProbabilityMeasure E)
    (hν : ConvexDominated (ν : Measure E) γ) : ν ∈ tripleSumLaws γ := by
  classical
  let f : C(E,ℝ) := ⟨norm,continuous_norm⟩
  have hy : Integrable id (ν : Measure E) := (integrable_norm_iff continuous_id.aestronglyMeasurable).mp
    (integrable_test hν (f := f) (convexOn_norm (convex_univ)) hγ.norm)
  have tight := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    (isTightMeasureSet_singleton (μ := (ν : Measure E)))
  obtain ⟨B,hB,hsmall⟩ : ∃ B : ℕ → Set E, (∀ n, IsCompact (B n)) ∧
      ∀ n, (ν : Measure E) (B n)ᶜ ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    choose B hB hsmall using fun n : ℕ => tight ((2 : ℝ≥0∞)⁻¹ ^ n) (pos_iff_ne_zero.mpr (pow_ne_zero n (by norm_num)))
    exact ⟨B,hB,fun n => hsmall n _ (mem_singleton _)⟩
  have hsum : (∑' n, (ν : Measure E) (B n)ᶜ) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hsmall)
    simp [ENNReal.tsum_geometric,ENNReal.one_sub_inv_two]
  choose Q hm K hK hr hfix hdec using fun n => truncate_barycentre ν (hB n) hy
  let μ (n : ℕ) := ν.map (hm n).aemeasurable
  have hmem (n) : μ n ∈ tripleSumLaws γ := by
    let Q' (x : E) : K n := ⟨Q n x, hr n (mem_range_self x)⟩
    have hm' : Measurable Q' := (hm n).subtype_mk
    let ξ := ν.map hm'.aemeasurable
    have he : (ξ : Measure (K n)).map Subtype.val = (ν : Measure E).map (Q n) := by
      change ((ν : Measure E).map Q').map Subtype.val = _
      rw [Measure.map_map measurable_subtype_coe hm']
      rfl
    have hd : ConvexDominated ((ξ : Measure (K n)).map Subtype.val) γ := by
      rw [he]
      intro g hg hgi
      rw [integral_map (hm n).aemeasurable g.continuous.aestronglyMeasurable]
      exact (hdec n g hg (integrable_test hν hg hgi)).trans (hν g hg hgi)
    obtain ⟨π,hπ,hs⟩ := ht _ (hK n) ξ hd
    exact ⟨π,hπ,hs.trans he⟩
  have ha : ∀ᵐ x ∂(ν : Measure E), Tendsto (fun n => Q n x) atTop (𝓝 x) := by
    filter_upwards [ae_eventually_notMem hsum] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [hx] with n hn
    exact (hfix n x (by simpa using hn)).symm
  have hlim := (tendstoInDistribution_of_ae_tendsto (fun n => (hm n).aemeasurable)
    (measurable_id.aemeasurable) ha).tendsto
  change Tendsto μ atTop (𝓝 (ν.map measurable_id.aemeasurable)) at hlim
  have he : ν.map measurable_id.aemeasurable = ν :=
    ProbabilityMeasure.toMeasure_injective Measure.map_id
  rw [he] at hlim
  exact (isCompact_tripleSumLaws γ).isClosed.mem_of_tendsto hlim (Eventually.of_forall hmem)

#print axioms triple_of_compact

open ProbabilityTheory

/-- Hua, Song and Tudose's three-Gaussian theorem, for arbitrary target laws
dominated by the standard finite-dimensional Gaussian in convex order. -/
theorem gaussian_triple (J : Finset ℕ) (ν : ProbabilityMeasure (J → ℝ))
    (hν : ConvexDominated (ν : Measure (J → ℝ)) (finiteGaussian J)) :
    ν ∈ tripleSumLaws (finiteGaussian J) := by
  apply triple_of_compact _ _ (compact_of_finite_contractions _ (fun _ hr hr' =>
    Green54Solved.finite_gaussian_triple J hr hr')) ν hν
  apply integrable_pi_iff.mpr
  intro j
  exact integrable_eval (μ := fun _ : J => gaussianReal 0 1) IsGaussian.integrable_id

#print axioms gaussian_triple

/-- The three-Gaussian theorem for a product indexed by any finite type. -/
theorem gaussian_triple_fintype (ι : Type*) [Fintype ι] (ν : ProbabilityMeasure (ι → ℝ))
    (hν : ConvexDominated (ν : Measure (ι → ℝ)) (Measure.pi (fun _ : ι => gaussianReal 0 1))) :
    ν ∈ tripleSumLaws (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  classical
  let J := Finset.range (Fintype.card ι)
  let e : ι ≃ J := Fintype.equivOfCardEq (by simp [J])
  let L := ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : J => ℝ) e
  let γ := Measure.pi (fun _ : ι => gaussianReal 0 1)
  have mp : MeasurePreserving L γ (finiteGaussian J) :=
    measurePreserving_piCongrLeft (fun _ : J => gaussianReal 0 1) e
  let ξ := ν.map L.continuous.measurable.aemeasurable
  have hd : ConvexDominated (ξ : Measure (J → ℝ)) (finiteGaussian J) := by
    intro f hf hi
    let g : C(ι → ℝ,ℝ) := ⟨f ∘ L,f.continuous.comp L.continuous⟩
    have hh := hν g (hf.comp_linearMap L.toLinearMap) (mp.integrable_comp_of_integrable hi)
    change (∫ x, f x ∂(ν : Measure (ι → ℝ)).map L) ≤ _
    rw [integral_map L.continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable]
    exact hh.trans_eq (mp.integral_comp L.toHomeomorph.isClosedEmbedding.measurableEmbedding _)
  obtain ⟨π,hπ,hs⟩ := gaussian_triple J ξ hd
  let Φ (z : Fin 3 → J → ℝ) (i : Fin 3) := L.symm (z i)
  have hm : Measurable Φ := measurable_pi_lambda _ fun i => L.symm.continuous.measurable.comp (measurable_pi_apply i)
  have back (μ : Measure (ι → ℝ)) : (μ.map L).map L.symm = μ := by
    rw [Measure.map_map L.symm.continuous.measurable L.continuous.measurable]
    simp [Function.comp_def]
  refine ⟨π.map hm.aemeasurable,?_,?_⟩
  · intro i
    change ((π : Measure (Fin 3 → J → ℝ)).map Φ).map _ = _
    rw [Measure.map_map (measurable_pi_apply i) hm]
    change (π : Measure (Fin 3 → J → ℝ)).map (L.symm ∘ fun z => z i) = _
    rw [← Measure.map_map L.symm.continuous.measurable (measurable_pi_apply i),hπ,← mp.map_eq,back]
  · let s (z : Fin 3 → ι → ℝ) := z 0 + z 1 + z 2
    let t (z : Fin 3 → J → ℝ) := z 0 + z 1 + z 2
    have hS : Measurable s := ((measurable_pi_apply 0).add (measurable_pi_apply 1)).add (measurable_pi_apply 2)
    have hT : Measurable t := ((measurable_pi_apply 0).add (measurable_pi_apply 1)).add (measurable_pi_apply 2)
    change ((π : Measure (Fin 3 → J → ℝ)).map Φ).map s = _
    rw [Measure.map_map hS hm]
    have he : s ∘ Φ = L.symm ∘ t := by
      funext z
      simp only [s,t,Φ,Function.comp_apply,map_add]
    rw [he,← Measure.map_map L.symm.continuous.measurable hT,hs]
    exact back _

#print axioms gaussian_triple_fintype

end Green54GeneralLaws
