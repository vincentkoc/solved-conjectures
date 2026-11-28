import Green54SymmetricBarrier
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Tactic

open Set Filter MeasureTheory
open scoped ENNReal Topology Pointwise
/-! Finite barycentric approximations for the compact-support case of the
three-Gaussian theorem in Green 54. -/

namespace Green54FiniteLaws
/-- Replacing each positive-mass partition cell by its barycentre decreases
the expectation of every integrable continuous convex test. -/
theorem partition_jensen {X E ι : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [Fintype ι] (ν : Measure X) [IsFiniteMeasure ν]
    (cell : ι → Set X) (hc : ∀ i, MeasurableSet (cell i)) (hd : Pairwise (fun i j => Disjoint (cell i) (cell j)))
    (hu : (⋃ i, cell i) = univ) {Y : X → E} (hY : Integrable Y ν) (f : C(E, ℝ))
    (hf : ConvexOn ℝ univ f) (hi : Integrable (f ∘ Y) ν) :
    ∑ i, ν.real (cell i) * f (⨍ x in cell i, Y x ∂ν) ≤ ∫ x, f (Y x) ∂ν := by
  have hcell (i : ι) : ν.real (cell i) * f (⨍ x in cell i, Y x ∂ν) ≤ ∫ x in cell i, f (Y x) ∂ν := by
    by_cases hz : ν (cell i) = 0
    · simp [measureReal_def, hz, Measure.restrict_eq_zero.mpr hz]
    have h := hf.map_set_average_le f.continuous.continuousOn isClosed_univ hz (measure_ne_top _ _)
      (ae_of_all _ fun _ => mem_univ _) hY.integrableOn hi.integrableOn
    have hh := mul_le_mul_of_nonneg_left h (measureReal_nonneg : 0 ≤ ν.real (cell i))
    exact hh.trans_eq (measure_smul_setAverage (μ := ν) (f ∘ Y) (measure_ne_top _ _))
  calc
    _ ≤ ∑ i, ∫ x in cell i, f (Y x) ∂ν := Finset.sum_le_sum fun i _ => hcell i
    _ = ∫ x in ⋃ i, cell i, f (Y x) ∂ν := (integral_iUnion_fintype hc hd (fun _ => hi.integrableOn)).symm
    _ = _ := by rw [hu, setIntegral_univ]

#print axioms partition_jensen

private theorem ball_partition {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {F : Set E} (hF : IsCompact F) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → F) (k : F → Fin n), Measurable k ∧
      ∀ x : F, dist x.val (c (k x)).val < ε := by
  classical
  obtain ⟨t, ht⟩ := hF.elim_finite_subcover (fun x : F => Metric.ball (x : E) ε)
    (fun _ => Metric.isOpen_ball) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self hε⟩)
  let c (i : Fin t.card) : F := (t.equivFin.symm i).val
  let B (i : Fin t.card) : Set F := Subtype.val ⁻¹' Metric.ball (c i).val ε
  have hB (i) : MeasurableSet (B i) := Metric.isOpen_ball.measurableSet.preimage measurable_subtype_coe
  have hcover : (⋃ i, B i) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨y, hy⟩ := mem_iUnion.mp (ht x.property)
    obtain ⟨hyt, hxy⟩ := mem_iUnion.mp hy
    refine mem_iUnion.mpr ⟨t.equivFin ⟨y, hyt⟩, ?_⟩
    change dist x.val (c (t.equivFin ⟨y, hyt⟩)).val < ε
    simpa only [c, Equiv.symm_apply_apply] using Metric.mem_ball.mp hxy
  have exists_cell (x : F) : ∃ i, x ∈ disjointed B i := by
    apply mem_iUnion.mp
    rw [iUnion_disjointed, hcover]
    trivial
  choose k hk using exists_cell
  refine ⟨t.card, c, k, measurable_to_countable' (fun i => ?_), ?_⟩
  · have he : k ⁻¹' {i} = disjointed B i := by
      ext x
      constructor
      · intro h
        exact (show k x = i from h) ▸ hk x
      · intro hx
        by_contra hn
        exact Set.disjoint_left.mp (disjoint_disjointed B (show k x ≠ i from hn)) (hk x) hx
    rw [he, disjointed_apply, Finset.sup_eq_iSup]
    exact (hB i).diff (MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => hB j)
  · intro x
    exact disjointed_subset B (k x) (hk x)

/-- A measurable finite-range barycentric approximation can be chosen uniformly close
on the whole compact support, with every convex test expectation weakly decreased. -/
theorem exists_finite_approx {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] {F : Set E} (hF : IsCompact F)
    (ν : ProbabilityMeasure F) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : F → E, Measurable Q ∧ (range Q).Finite ∧ (∀ x : F, dist (Q x) x.val < ε) ∧
      ∀ f : C(E, ℝ), ConvexOn ℝ univ f → ∫ x, f (Q x) ∂(ν : Measure F) ≤
        ∫ x, f x.val ∂(ν : Measure F) := by
  classical
  let : CompactSpace F := isCompact_iff_compactSpace.mp hF
  obtain ⟨n, c, k, hk, hdist⟩ := ball_partition hF (half_pos hε)
  let cell (i : Fin n) := k ⁻¹' {i}
  have hc (i) : MeasurableSet (cell i) := (measurableSet_singleton i).preimage hk
  have hd : Pairwise (fun i j => Disjoint (cell i) (cell j)) := by
    intro i j hij
    exact (Set.disjoint_singleton.mpr hij).preimage k
  have hu : (⋃ i, cell i) = univ := eq_univ_of_forall fun x => mem_iUnion.mpr ⟨k x, rfl⟩
  let μ : Measure F := ν
  let Y (x : F) : E := x.val
  have hy : Integrable Y μ := continuous_subtype_val.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  let b (i : Fin n) := if μ (cell i) = 0 then (c i).val else ⨍ x in cell i, Y x ∂μ
  have bloc (i) : b i ∈ Metric.closedBall (c i).val (ε/2) := by
    by_cases h0 : μ (cell i) = 0
    · simpa [b, h0] using Metric.mem_closedBall_self (x := (c i).val) (half_pos hε).le
    · rw [show b i = ⨍ x in cell i, Y x ∂μ by simp [b, h0]]
      apply (convex_closedBall _ _).set_average_mem Metric.isClosed_closedBall h0
        (measure_ne_top _ _) _ hy.integrableOn
      filter_upwards [ae_restrict_mem (μ := μ) (hc i)] with x hx
      exact (show k x = i from hx) ▸ (hdist x).le
  let Q := b ∘ k
  have hQ : Measurable Q := (measurable_of_finite b).comp hk
  refine ⟨Q, hQ, (finite_range b).subset (range_comp_subset_range _ _), ?_, ?_⟩
  · intro x
    calc
      dist (Q x) x.val ≤ dist (b (k x)) (c (k x)).val + dist (c (k x)).val x.val := dist_triangle ..
      _ < ε := by
        have h₁ := Metric.mem_closedBall.mp (bloc (k x))
        have h₂ := hdist x
        rw [dist_comm (c (k x)).val]
        linarith
  · intro f hf
    have hi : Integrable (f ∘ Y) μ := (f.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
    have hj := partition_jensen μ cell hc hd hu hy f hf hi
    have he (i) : ∫ x in cell i, f (Q x) ∂μ = μ.real (cell i) * f (⨍ x in cell i, Y x ∂μ) := by
      by_cases h0 : μ (cell i) = 0
      · simp [measureReal_def, h0, Measure.restrict_eq_zero.mpr h0]
      · calc
          _ = ∫ _ in cell i, f (b i) ∂μ := setIntegral_congr_fun (hc i) (fun x hx => by
            change f (b (k x)) = f (b i)
            rw [show k x = i from hx])
          _ = _ := by simp [b, h0, smul_eq_mul]
    have hfi (i) : IntegrableOn (fun x => f (Q x)) (cell i) μ :=
      (integrable_const (f (b i))).congr <| by
        filter_upwards [ae_restrict_mem (μ := μ) (hc i)] with x hx
        change f (b i) = f (b (k x))
        rw [show k x = i from hx]
    calc
      _ = ∫ x in ⋃ i, cell i, f (Q x) ∂μ := by rw [hu, setIntegral_univ]
      _ = ∑ i, ∫ x in cell i, f (Q x) ∂μ := integral_iUnion_fintype hc hd hfi
      _ ≤ _ := by simpa only [he] using hj

#print axioms exists_finite_approx

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- The joint probability laws with three prescribed marginals form a weakly compact set. -/
theorem isCompact_couplings (γ : ProbabilityMeasure E) :
    IsCompact {π : ProbabilityMeasure (Fin 3 → E) |
      ∀ i, (π : Measure (Fin 3 → E)).map (fun z => z i) = (γ : Measure E)} := by
  let S : Set (ProbabilityMeasure (Fin 3 → E)) :=
    {π | ∀ i, (π : Measure (Fin 3 → E)).map (fun z => z i) = (γ : Measure E)}
  have hclosed : IsClosed S := by
    have hd : S = ⋂ i : Fin 3, {π : ProbabilityMeasure (Fin 3 → E) |
        π.map (continuous_apply i).measurable.aemeasurable = γ} := by
      ext π
      simp only [S, mem_ofPred_eq, mem_iInter]
      exact forall_congr' fun i => ⟨fun h => ProbabilityMeasure.toMeasure_injective h,
        fun h => congrArg (fun ν : ProbabilityMeasure E => (ν : Measure E)) h⟩
    rw [hd]
    exact isClosed_iInter fun i => isClosed_eq (ProbabilityMeasure.continuous_map (continuous_apply i)) continuous_const
  change IsCompact S
  rw [← hclosed.closure_eq]
  apply isCompact_closure_of_isTightMeasureSet
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  have ht := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    (isTightMeasureSet_singleton (μ := (γ : Measure E)))
  obtain ⟨K, hK, hmass⟩ := ht (ε / 3) (ENNReal.div_pos hε.ne' (by norm_num))
  refine ⟨univ.pi (fun _ : Fin 3 => K), isCompact_univ_pi (fun _ => hK), ?_⟩
  rintro _ ⟨π, hπ, rfl⟩
  let bad (i : Fin 3) := (fun z : Fin 3 → E => z i) ⁻¹' Kᶜ
  have hb (i) : (π : Measure (Fin 3 → E)) (bad i) ≤ ε / 3 := by
    rw [show (π : Measure (Fin 3 → E)) (bad i) = (γ : Measure E) Kᶜ by
      rw [← hπ i, Measure.map_apply (measurable_pi_apply i) hK.measurableSet.compl]]
    exact hmass _ (mem_singleton _)
  calc
    _ ≤ (π : Measure (Fin 3 → E)) (⋃ i, bad i) := by
      apply measure_mono
      intro z hz
      simp_all only [mem_compl_iff, mem_univ_pi, not_forall, mem_iUnion, bad, mem_preimage]
    _ ≤ ∑ i, (π : Measure (Fin 3 → E)) (bad i) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin 3, ε / 3 := Finset.sum_le_sum fun i _ => hb i
    _ = ε := by
      rw [Fin.sum_univ_three, ← two_mul, ← add_one_mul, show (2 + 1 : ℝ≥0∞) = 3 by norm_num]
      exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)

#print axioms isCompact_couplings

/-- Laws of sums of three vectors with the same prescribed marginal. -/
def tripleSumLaws (γ : Measure E) : Set (ProbabilityMeasure E) :=
  {μ | ∃ π : ProbabilityMeasure (Fin 3 → E),
    (∀ i : Fin 3, (π : Measure (Fin 3 → E)).map (fun z => z i) = γ) ∧
    (π : Measure (Fin 3 → E)).map (fun z => z 0 + z 1 + z 2) = (μ : Measure E)}

/-- The laws of the sums inherit weak compactness from their couplings. -/
theorem isCompact_tripleSumLaws (γ : Measure E) [IsProbabilityMeasure γ] : IsCompact (tripleSumLaws γ) := by
  let Γ : ProbabilityMeasure E := ⟨γ, inferInstance⟩
  let σ (z : Fin 3 → E) := z 0 + z 1 + z 2
  have hσ : Continuous σ := ((continuous_apply 0).add (continuous_apply 1)).add (continuous_apply 2)
  convert (isCompact_couplings Γ).image (ProbabilityMeasure.continuous_map hσ) using 1
  ext μ
  constructor
  · rintro ⟨π, hπ, hs⟩
    exact ⟨π, hπ, ProbabilityMeasure.toMeasure_injective hs⟩
  · rintro ⟨π, hπ, rfl⟩
    exact ⟨π, hπ, rfl⟩

#print axioms isCompact_tripleSumLaws

open Green54ConvexTests
variable [NormedSpace ℝ E]

/-- Finite-support case of the triple decomposition. Each of the three marginals is γ. -/
def FiniteTripleDecomposition (γ : Measure E) (bound : Measure E := γ) : Prop :=
  ∀ (F : Set E), F.Finite → ∀ ν : ProbabilityMeasure F,
    ConvexDominated ((ν : Measure F).map Subtype.val) bound →
    ν.map measurable_subtype_coe.aemeasurable ∈ tripleSumLaws γ

omit [CompleteSpace E] [SecondCountableTopology E] [BorelSpace E] in
private theorem mem_tripleSumLaws_of_finite_range {γ bound : Measure E}
    (h : FiniteTripleDecomposition γ bound) {X : Type*} [MeasurableSpace X]
    (ν : ProbabilityMeasure X) {Q : X → E} (hm : Measurable Q) (hr : (range Q).Finite)
    (hdom : ConvexDominated ((ν : Measure X).map Q) bound) :
    ν.map hm.aemeasurable ∈ tripleSumLaws γ := by
  let ξ := ν.map hm.rangeFactorization.aemeasurable
  have hmap : (ξ : Measure (range Q)).map Subtype.val = (ν : Measure X).map Q := by
    change ((ν : Measure X).map (rangeFactorization Q)).map Subtype.val = _
    rw [Measure.map_map measurable_subtype_coe hm.rangeFactorization]
    rfl
  obtain ⟨π, hπ, hs⟩ := h _ hr ξ (hmap ▸ hdom)
  exact ⟨π, hπ, hs.trans hmap⟩

/-- The finite-support and compact-support triple decomposition statements are equivalent
for any reference probability law on a separable Banach space. -/
theorem compact_iff_finite (γ : Measure E) [IsProbabilityMeasure γ] :
    CompactTripleDecomposition γ ↔ FiniteTripleDecomposition γ := by
  constructor
  · intro h F hF
    exact h F hF.isCompact
  intro h F hF ν hν
  let ε (n : ℕ) := 1 / ((n : ℝ) + 1)
  have hpos (n) : 0 < ε n := by dsimp [ε]; positivity
  choose Q hm hr hd hj using fun n => exists_finite_approx hF ν (hpos n)
  let μ (n : ℕ) := ν.map (hm n).aemeasurable
  let target := ν.map measurable_subtype_coe.aemeasurable
  have hmem (n) : μ n ∈ tripleSumLaws γ := by
    apply mem_tripleSumLaws_of_finite_range h ν (hm n) (hr n)
    intro f hf hi
    have hne := hν f hf hi
    rw [integral_map measurable_subtype_coe.aemeasurable f.continuous.aestronglyMeasurable] at hne
    rw [integral_map (hm n).aemeasurable f.continuous.aestronglyMeasurable]
    exact (hj n f hf).trans hne
  have hlim : Tendsto μ atTop (𝓝 target) := by
    apply (tendstoInDistribution_of_ae_tendsto (fun n => (hm n).aemeasurable)
      measurable_subtype_coe.aemeasurable _).tendsto
    exact ae_of_all _ fun x => tendsto_iff_dist_tendsto_zero.mpr
      (squeeze_zero (fun _ => dist_nonneg) (fun n => (hd n x).le) tendsto_one_div_add_atTop_nhds_zero_nat)
  exact (isCompact_tripleSumLaws γ).isClosed.mem_of_tendsto hlim (Eventually.of_forall hmem)

#print axioms compact_iff_finite

/-- It suffices to construct the triple when the finite target is convex-dominated
by a strict contraction of the reference law. The three marginals retain the original law. -/
theorem compact_of_finite_contractions (γ : Measure E) [IsProbabilityMeasure γ]
    (h : ∀ r : ℝ, 0 < r → r < 1 → FiniteTripleDecomposition γ (γ.map (fun x => r • x))) :
    CompactTripleDecomposition γ := by
  apply (compact_iff_finite γ).mpr
  intro F hF ν hν
  let : Finite F := hF.to_subtype
  let r (n : ℕ) := (n : ℝ) / (n + 1)
  let Q (n : ℕ) (x : F) : E := r n • x.val
  have hm (n) : Measurable (Q n) := (continuous_const.smul continuous_subtype_val).measurable
  let μ (n : ℕ) := ν.map (hm n).aemeasurable
  have hlim : Tendsto μ atTop (𝓝 (ν.map measurable_subtype_coe.aemeasurable)) := by
    apply (tendstoInDistribution_of_ae_tendsto (fun n => (hm n).aemeasurable)
      measurable_subtype_coe.aemeasurable _).tendsto
    exact ae_of_all _ fun x => by
      simpa only [one_smul] using (tendsto_natCast_div_add_atTop (1 : ℝ)).smul
        (tendsto_const_nhds (x := x.val) (f := atTop))
  apply (isCompact_tripleSumLaws γ).isClosed.mem_of_tendsto hlim
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hr : 0 < r n := div_pos (by exact_mod_cast hn) (by positivity)
  have hr' : r n < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  apply mem_tripleSumLaws_of_finite_range (h _ hr hr') ν (hm n) (finite_range _)
  intro f hf hi
  let D : E →ₗ[ℝ] E := r n • LinearMap.id
  have hD : Continuous D := continuous_const.smul continuous_id
  let g : C(E, ℝ) := ⟨f ∘ D, f.continuous.comp hD⟩
  have hle := hν g (hf.comp_linearMap D) (hi.comp_aemeasurable hD.measurable.aemeasurable)
  rw [integral_map measurable_subtype_coe.aemeasurable g.continuous.aestronglyMeasurable] at hle
  change (∫ x, f x ∂(ν : Measure F).map (Q n)) ≤ ∫ x, f x ∂γ.map D
  rw [integral_map (hm n).aemeasurable f.continuous.aestronglyMeasurable,
    integral_map hD.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  exact hle

#print axioms compact_of_finite_contractions

open Green54Projections

/-- The pinned Green 54 statement follows from the finite-atomic Gaussian triple theorem
with slack in convex domination. -/
theorem green_54_of_finite_laws
    (ht : ∀ I : Finset ℕ, I.Nonempty → ∀ r : ℝ, 0 < r → r < 1 →
      FiniteTripleDecomposition (finiteGaussian I) ((finiteGaussian I).map (fun x => r • x))) :
    ∀ K : Set (ℕ → ℝ), IsCompact K → Balanced ℝ K → (0.99 : ℝ≥0∞) ≤ gaussian K →
    ∃ C : Set (ℕ → ℝ), IsCompact C ∧ Convex ℝ C ∧ C ⊆ (10 : ℕ) • K ∧
      (0.01 : ℝ≥0∞) ≤ gaussian C :=
  Green54Symmetric.green_54_of_triple fun I hI => compact_of_finite_contractions _ (ht I hI)

#print axioms green_54_of_finite_laws

end Green54FiniteLaws
