import Green54GaussianProjections
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

open Set MeasureTheory TopologicalSpace CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal Pointwise

/-! The compact separation argument used for Gaussian convexification. -/

namespace Green54ConvexTests
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A convex family of continuous tests, each nonpositive somewhere on a compact space,
admits a common probability measure with nonpositive expectations. -/
theorem probability_of_convex_tests (Y : Set C(X, ℝ)) (hY : Convex ℝ Y) (h0 : 0 ∈ Y)
    (hmin : ∀ f ∈ Y, ∃ x, f x ≤ 0) :
    ∃ μ : ProbabilityMeasure X, ∀ f ∈ Y, (∫ x, f x ∂(μ : Measure X)) ≤ 0 := by
  let P : Set C(X, ℝ) := {f | ∀ x, 0 < f x}
  have hP : Convex ℝ P := by
    intro f hf g hg a b ha hb hab x
    exact (convex_Ioi (𝕜 := ℝ) (0 : ℝ)) (hf x) (hg x) ha hb hab
  have hopen : IsOpen P := by
    simpa [P, Set.mapsTo_univ_iff, Set.range_subset_iff] using
      (ContinuousMap.isOpen_setOfPred_range_subset (X := X) (isOpen_Ioi (a := (0 : ℝ))))
  have hd : Disjoint P Y := Set.disjoint_left.mpr (by
    intro f hf hy
    obtain ⟨x, hx⟩ := hmin _ hy
    exact (hf x).not_ge hx)
  obtain ⟨l, u, hup, hlo⟩ := geometric_hahn_banach_open hP hopen hY hd
  have hcl {g : C(X, ℝ)} (hg : 0 ≤ g) : g ∈ closure P := by
    let shift (t : ℝ) := g + t • (1 : C(X, ℝ))
    have hc : Continuous shift := by dsimp [shift]; fun_prop
    have maps : MapsTo shift (Ioi 0) P := by
      intro t ht x
      change 0 < g x + t * 1
      simpa using add_pos_of_nonneg_of_pos (hg x) ht
    have hz : (0 : ℝ) ∈ closure (Ioi 0) := by simp [closure_Ioi]
    simpa [shift] using maps.closure hc hz
  have hnonneg {g : C(X, ℝ)} (hg : 0 ≤ g) : l g ≤ u :=
    (closure_minimal (fun x hx => (hup x hx).le) (isClosed_le l.continuous continuous_const)) (hcl hg)
  have hu : u = 0 := le_antisymm (by simpa using hlo 0 h0) (by simpa using hnonneg (g := 0) le_rfl)
  subst u
  have hone : l 1 < 0 := hup 1 (fun _ => zero_lt_one)
  let F : C(X, ℝ) →ₗ[ℝ] ℝ := (l 1)⁻¹ • l.toLinearMap
  have hmono : Monotone F := by
    intro f g h
    have hle := hnonneg (g := g - f) (fun x => sub_nonneg.mpr (h x))
    rw [map_sub] at hle
    change (l 1)⁻¹ * l f ≤ (l 1)⁻¹ * l g
    exact mul_le_mul_of_nonpos_left (sub_nonpos.mp hle) (inv_nonpos.mpr hone.le)
  have hunit : F 1 = 1 := by change (l 1)⁻¹ * l 1 = 1; exact inv_mul_cancel₀ hone.ne
  have htests {f : C(X, ℝ)} (hf : f ∈ Y) : F f ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.mpr hone.le) (hlo f hf)
  let L : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun f => F f.toContinuousMap
      map_add' := fun f g => F.map_add f.toContinuousMap g.toContinuousMap
      map_smul' := fun c f => F.map_smul c f.toContinuousMap
      monotone' := fun _ _ h => hmono h }
  let μ := RealRMK.rieszMeasure L
  have hrep (f : C(X, ℝ)) : (∫ x, f x ∂μ) = F f :=
    RealRMK.integral_rieszMeasure L (CompactlySupportedContinuousMap.continuousMapEquiv f)
  have hprob : IsProbabilityMeasure μ := by
    constructor
    apply (ENNReal.toReal_eq_one_iff _).mp
    simpa [Measure.real] using (hrep 1).trans hunit
  exact ⟨⟨μ, hprob⟩, fun f hf => (hrep f).trans_le (htests hf)⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Convex order for a compactly supported first measure, tested against the continuous
convex functions integrable for the reference measure. -/
def ConvexDominated (ν γ : Measure E) : Prop := ∀ f : C(E, ℝ),
  ConvexOn ℝ univ f → Integrable f γ → ∫ x, f x ∂ν ≤ ∫ x, f x ∂γ

/-- If no law on a compact forbidden set lies below the reference law in convex order,
one continuous convex test separates every point of that set from the reference mean. -/
theorem exists_barrier (γ : Measure E) {F : Set E} (hF : IsCompact F)
    (hbad : ∀ ν : ProbabilityMeasure F, ¬ ConvexDominated ((ν : Measure F).map Subtype.val) γ) :
    ∃ f : C(E, ℝ), ConvexOn ℝ univ f ∧ Integrable f γ ∧ ∀ x ∈ F, ∫ y, f y ∂γ < f x := by
  classical
  let : CompactSpace F := isCompact_iff_compactSpace.mp hF
  let centered (f : C(E, ℝ)) := f.restrict F - ContinuousMap.const F (∫ x, f x ∂γ)
  let tests : Set C(E, ℝ) := {f | ConvexOn ℝ univ f ∧ Integrable f γ}
  let Y := centered '' tests
  have h0 : 0 ∈ Y := by
    refine ⟨0, ⟨convexOn_const 0 (convex_univ), integrable_zero _ _ _⟩, ?_⟩
    ext x
    simp [centered]
  have hY : Convex ℝ Y := by
    rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩ a b ha hb _
    have hi := (hf.2.smul a).add (hg.2.smul b)
    refine ⟨a • f + b • g, ⟨(hf.1.smul ha).add (hg.1.smul hb), hi⟩, ?_⟩
    ext x
    change a * f x + b * g x - (∫ y, a • f y + b • g y ∂γ) =
      a * (f x - ∫ y, f y ∂γ) + b * (g x - ∫ y, g y ∂γ)
    have hfa : Integrable (fun y => a • f y) γ := hf.2.smul a
    have hgb : Integrable (fun y => b • g y) γ := hg.2.smul b
    rw [integral_add hfa hgb, integral_smul, integral_smul]
    simp only [smul_eq_mul]
    ring
  by_contra! hn
  have hmin : ∀ g ∈ Y, ∃ x, g x ≤ 0 := by
    rintro g ⟨f, ⟨hcv, hi⟩, rfl⟩
    obtain ⟨x, hx, he⟩ := hn f hcv hi
    exact ⟨⟨x, hx⟩, sub_nonpos.mpr he⟩
  obtain ⟨ν, hν⟩ := probability_of_convex_tests Y hY h0 hmin
  apply hbad ν
  intro f hcv hi
  have ht := hν (centered f) ⟨f, ⟨hcv, hi⟩, rfl⟩
  have hint : Integrable (fun x : F => f x) (ν : Measure F) :=
    (f.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ x : F, f x - (∫ y, f y ∂γ) ∂(ν : Measure F)) ≤ 0 at ht
  rw [integral_sub hint (integrable_const _), integral_const] at ht
  rw [integral_map measurable_subtype_coe.aemeasurable f.continuous.aestronglyMeasurable]
  simpa using sub_nonpos.mp ht

/-- The compact-support case of the three-Gaussian theorem, written in terms of joint laws.
The three marginals may be dependent. -/
def CompactTripleDecomposition (γ : Measure E) : Prop :=
  ∀ (F : Set E), IsCompact F → ∀ ν : ProbabilityMeasure F,
    ConvexDominated ((ν : Measure F).map Subtype.val) γ →
    ∃ π : ProbabilityMeasure (Fin 3 → E),
      (∀ i : Fin 3, (π : Measure (Fin 3 → E)).map (fun z => z i) = γ) ∧
      (π : Measure (Fin 3 → E)).map (fun z => z 0 + z 1 + z 2) = (ν : Measure F).map Subtype.val

/-- A joint law with equal marginals assigns positive mass to the event that all
three coordinates lie in a set of marginal probability greater than two thirds. -/
theorem triple_hit {V : Type*} [MeasurableSpace V] (γ : Measure V) [IsProbabilityMeasure γ] (π : ProbabilityMeasure (Fin 3 → V))
    (hπ : ∀ i : Fin 3, (π : Measure (Fin 3 → V)).map (fun z => z i) = γ)
    {A : Set V} (hA : MeasurableSet A) (hm : 2 / 3 < γ.real A) :
    0 < (π : Measure (Fin 3 → V)).real {z | z 0 ∈ A ∧ z 1 ∈ A ∧ z 2 ∈ A} := by
  let miss (i : Fin 3) := (fun z : Fin 3 → V => z i) ⁻¹' Aᶜ
  have hmiss (i : Fin 3) : (π : Measure (Fin 3 → V)).real (miss i) = 1 - γ.real A := by
    rw [← probReal_compl_eq_one_sub hA, Measure.real, Measure.real, ← hπ i,
      Measure.map_apply (measurable_pi_apply i) hA.compl]
  let U := miss 0 ∪ (miss 1 ∪ miss 2)
  have hU : MeasurableSet U :=
    (hA.compl.preimage (measurable_pi_apply 0)).union
      ((hA.compl.preimage (measurable_pi_apply 1)).union (hA.compl.preimage (measurable_pi_apply 2)))
  have hunion := measureReal_union_le (μ := (π : Measure (Fin 3 → V))) (miss 0) (miss 1 ∪ miss 2)
  have hpair := measureReal_union_le (μ := (π : Measure (Fin 3 → V))) (miss 1) (miss 2)
  rw [hmiss] at hunion
  rw [hmiss, hmiss] at hpair
  have he : {z : Fin 3 → V | z 0 ∈ A ∧ z 1 ∈ A ∧ z 2 ∈ A} = Uᶜ := by
    ext z
    simp [U, miss]
  rw [he, probReal_compl_eq_one_sub hU]
  dsimp only [U]
  linarith

/-- The three-Gaussian theorem yields a single convex barrier on every compact set
disjoint from the triple sum. This is the separation step in Mazhar's Theorem 1.2. -/
theorem triple_sum_barrier [SecondCountableTopology E] (γ : Measure E) [IsProbabilityMeasure γ]
    (htriple : CompactTripleDecomposition γ) {A F : Set E}
    (hA : MeasurableSet A) (hm : 2 / 3 < γ.real A) (hF : IsCompact F)
    (hdisj : Disjoint F (A + A + A)) :
    ∃ f : C(E, ℝ), ConvexOn ℝ univ f ∧ Integrable f γ ∧ ∀ x ∈ F, ∫ y, f y ∂γ < f x := by
  apply exists_barrier γ hF
  intro ν hν
  obtain ⟨π, hπ, hsum⟩ := htriple F hF ν hν
  have hnull : (π : Measure (Fin 3 → E)).real ((fun z => z 0 + z 1 + z 2) ⁻¹' Fᶜ) = 0 := by
    have hmeas : Measurable (fun z : Fin 3 → E => z 0 + z 1 + z 2) :=
      ((continuous_apply 0 |>.add (continuous_apply 1)).add (continuous_apply 2)).measurable
    rw [Measure.real, ← Measure.map_apply hmeas hF.isClosed.measurableSet.compl, hsum,
      Measure.map_apply measurable_subtype_coe hF.isClosed.measurableSet.compl]
    simp
  have hsub : {z : Fin 3 → E | z 0 ∈ A ∧ z 1 ∈ A ∧ z 2 ∈ A} ⊆
      (fun z => z 0 + z 1 + z 2) ⁻¹' Fᶜ := by
    intro z hz hmem
    exact Set.disjoint_left.mp hdisj hmem (add_mem_add (add_mem_add hz.1 hz.2.1) hz.2.2)
  exact (triple_hit γ π hπ hA hm).not_ge ((measureReal_mono hsub).trans hnull.le)

#print axioms probability_of_convex_tests
#print axioms exists_barrier
#print axioms triple_hit
#print axioms triple_sum_barrier

/-- A median bound for continuous convex tests, in the form used by Mazhar. -/
def ConvexSublevelMass (γ : Measure E) (β : ℝ≥0∞) : Prop :=
  ∀ f : C(E, ℝ), ConvexOn ℝ univ f → Integrable f γ →
    β ≤ γ {x | f x ≤ ∫ y, f y ∂γ}

/-- Compact-input convexification from triple decomposition and the convex sublevel bound.
The argument needs neither symmetry of the starting set nor an independent coupling. -/
theorem convex_core_of_triple_and_sublevel {ι : Type*} [Fintype ι]
    (γ : Measure (ι → ℝ)) [IsProbabilityMeasure γ] {β : ℝ≥0∞} (hβ : 0 < β)
    (htriple : CompactTripleDecomposition γ) (hmedian : ConvexSublevelMass γ β)
    {A : Set (ι → ℝ)} (hA : IsCompact A) (hm : 2 / 3 < γ.real A) :
    ∃ C : Set (ι → ℝ), IsCompact C ∧ Convex ℝ C ∧ C ⊆ A + A + A ∧ β ≤ γ C := by
  let D := A + A + A
  have hD : IsCompact D := (hA.add hA).add hA
  apply Green54Projections.compact_convex_of_thickenings γ hD hβ
  intro r hr b hb
  obtain ⟨L, _, hL, hLmass⟩ := MeasurableSet.univ.exists_isCompact_sdiff_lt
    (measure_ne_top γ _) (tsub_pos_of_lt hb).ne'
  obtain ⟨R, hLR⟩ := hL.isBounded.subset_closedBall 0
  let B := Metric.closedBall (0 : ι → ℝ) R
  have hB : IsCompact B := isCompact_closedBall _ _
  have hsmall : γ Bᶜ < β - b := (measure_mono (compl_subset_compl.mpr hLR)).trans_lt
    (by simpa only [← Set.compl_eq_univ_sdiff] using hLmass)
  let F := B \ Metric.thickening r D
  have hF : IsCompact F := hB.diff Metric.isOpen_thickening
  have hd : Disjoint F D := Set.disjoint_left.mpr (by
    intro x hx hxD
    exact hx.2 (Metric.self_subset_thickening hr D hxD))
  obtain ⟨f, hcv, hi, hsep⟩ := triple_sum_barrier γ htriple hA.isClosed.measurableSet hm hF hd
  let S := {x | f x ≤ ∫ y, f y ∂γ}
  have hS : IsClosed S := isClosed_le f.continuous continuous_const
  have hSv : Convex ℝ S := by simpa [S] using hcv.convex_le (∫ y, f y ∂γ)
  refine ⟨S ∩ B, hB.inter_left hS, hSv.inter (convex_closedBall _ _), ?_, ?_⟩
  · intro x hx
    apply Metric.thickening_subset_cthickening r D
    by_contra hnot
    exact (hsep x ⟨hx.2, hnot⟩).not_ge hx.1
  · by_contra! hlt
    have he := ENNReal.add_lt_add hlt ((measure_mono (show S \ B ⊆ Bᶜ from fun _ hx => hx.2)).trans_lt hsmall)
    rw [measure_inter_add_sdiff S hB.isClosed.measurableSet, add_tsub_cancel_of_le hb.le] at he
    exact he.not_ge (hmedian f hcv hi)

#print axioms convex_core_of_triple_and_sublevel

open ProbabilityTheory Green54Projections
open scoped NNReal

noncomputable abbrev finiteGaussian (I : Finset ℕ) := Measure.pi (fun _ : I => gaussianReal 0 1)

/-- Compact-support, finite-dimensional instance of Hua–Song–Tudose, Theorem 1.1. -/
def GaussianTripleDecomposition : Prop :=
  ∀ I : Finset ℕ, I.Nonempty → CompactTripleDecomposition (finiteGaussian I)

/-- Kwapień's Gaussian convex mean–median comparison at probability one half. -/
def GaussianConvexMedian : Prop :=
  ∀ I : Finset ℕ, I.Nonempty → ConvexSublevelMass (finiteGaussian I) (1 / 2)

/-- The mass conclusion of Mazhar's finite three-sum theorem from its two analytic inputs. -/
theorem finite_three_of_analytic_inputs (ht : GaussianTripleDecomposition) (hm : GaussianConvexMedian) :
    FiniteThreeSum := by
  intro I hI A hA hmass
  have hreal := (ENNReal.toReal_lt_toReal (by finiteness) (measure_ne_top _ _)).mpr hmass
  apply convex_core_of_triple_and_sublevel (finiteGaussian I) (by norm_num) (ht I hI) (hm I hI) hA
  simpa [Measure.real, ENNReal.toReal_div] using hreal

/-- The countable triple-sum bound from the finite Gaussian decomposition and median estimates. -/
theorem gaussian_three_of_analytic_inputs (ht : GaussianTripleDecomposition) (hm : GaussianConvexMedian)
    {K : Set Space} (hK : IsCompact K) (hμ : (2 / 3 : ℝ≥0∞) < gaussian K) :
    ∃ C : Set Space, IsCompact C ∧ Convex ℝ C ∧ C ⊆ K + K + K ∧ (1 / 2 : ℝ≥0∞) ≤ gaussian C :=
  gaussian_three_of_finite (finite_three_of_analytic_inputs ht hm) hK hμ

/-- The exact positive DeepMind statement under the two finite analytic theorems. -/
theorem green_54_of_analytic_inputs (ht : GaussianTripleDecomposition) (hm : GaussianConvexMedian) :
    ∀ K : Set (ℕ → ℝ), IsCompact K → Balanced ℝ K → (0.99 : ℝ≥0∞) ≤ gaussian K →
    ∃ C : Set (ℕ → ℝ), IsCompact C ∧ Convex ℝ C ∧ C ⊆ (10 : ℕ) • K ∧
      (0.01 : ℝ≥0∞) ≤ gaussian C := by
  intro K hK hb hμ
  have hl : (2 / 3 : ℝ≥0∞) < 0.99 := by
    change 2 / 3 < ((0.99 : ℝ≥0) : ℝ≥0∞)
    rw [← ENNReal.toReal_lt_toReal (by finiteness) ENNReal.coe_ne_top, ENNReal.coe_toReal]
    norm_num [ENNReal.toReal_div]
  have hs : (0.01 : ℝ≥0∞) ≤ 1 / 2 := by
    change ((0.01 : ℝ≥0) : ℝ≥0∞) ≤ 1 / 2
    rw [← ENNReal.toReal_le_toReal ENNReal.coe_ne_top (by finiteness), ENNReal.coe_toReal]
    norm_num [ENNReal.toReal_div]
  obtain ⟨C, hc, hv, hsub, hmass⟩ := gaussian_three_of_analytic_inputs ht hm hK (hl.trans_le hμ)
  have hz := hb.zero_mem (nonempty_of_measure_ne_zero (s := K) (bot_le.trans_lt (hl.trans_le hμ)).ne')
  have h3 : C ⊆ (3 : ℕ) • K := by simpa [succ_nsmul] using hsub
  refine ⟨C, hc, hv, ?_, hs.trans hmass⟩
  intro x hx
  rw [show (10 : ℕ) = 3 + 7 by decide, add_nsmul]
  have hpad := Set.nsmul_mem_nsmul (n := 7) hz
  simpa using Set.add_mem_add (h3 hx) hpad

#print axioms finite_three_of_analytic_inputs
#print axioms gaussian_three_of_analytic_inputs
#print axioms green_54_of_analytic_inputs

end Green54ConvexTests
