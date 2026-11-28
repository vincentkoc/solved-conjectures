import Green54ConvexTests
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open Set MeasureTheory Filter ProbabilityTheory
open Green54ConvexTests
open scoped Pointwise
open scoped ENNReal
namespace Green54Symmetric
/-- Markov's inequality at twice the mean, including the zero-mean case. -/
theorem mass_at_twice_mean {X : Type*} [MeasurableSpace X] (γ : Measure X) [IsProbabilityMeasure γ]
    {g : X → ℝ} (hg : Measurable g) (hpos : 0 ≤ g) (hi : Integrable g γ) :
    (1 / 2 : ℝ≥0∞) ≤ γ {x | g x ≤ 2 * ∫ y, g y ∂γ} := by
  let m := ∫ y, g y ∂γ
  have hm : 0 ≤ m := integral_nonneg hpos
  by_cases hz : m = 0
  · have hae := (integral_eq_zero_iff_of_nonneg hpos hi).mp hz
    have he : {x | g x ≤ 2 * m} =ᵐ[γ] univ := by
      filter_upwards [hae] with x hx
      change (g x ≤ 2 * m) = (x ∈ (univ : Set X))
      simp [show g x = 0 from hx, hz]
    rw [show (∫ y, g y ∂γ) = m from rfl, measure_congr he, measure_univ]
    norm_num
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hpos) hi (2 * m)
  let S := {x | g x ≤ 2 * m}
  have hSc : γ.real Sᶜ ≤ γ.real {x | 2 * m ≤ g x} := measureReal_mono (fun x h => le_of_lt (lt_of_not_ge (show ¬g x ≤ 2 * m from h)))
  have hSm : MeasurableSet S := measurableSet_le hg measurable_const
  rw [probReal_compl_eq_one_sub hSm] at hSc
  change 2 * m * _ ≤ m at hmarkov
  have hu : γ.real {x | 2 * m ≤ g x} ≤ 1 / 2 := by
    apply (mul_le_mul_iff_right₀ (show 0 < 2 * m by positivity)).mp
    nlinarith only [hmarkov]
  apply (ENNReal.toReal_le_toReal (by finiteness) (measure_ne_top _ _)).mp
  change (1 / 2 : ℝ≥0∞).toReal ≤ γ.real S
  norm_num [ENNReal.toReal_div]
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- Symmetrizing a separating convex test preserves the strict gap on paired points. -/
theorem even_barrier (γ : Measure E) [IsProbabilityMeasure γ] (hn : MeasurePreserving (fun x : E => -x) γ γ)
    {F : Set E} {f : C(E, ℝ)} (hcv : ConvexOn ℝ univ f) (hi : Integrable f γ)
    (hp : ∀ x ∈ F, ∫ y, f y ∂γ < f x) (hm : ∀ x ∈ F, ∫ y, f y ∂γ < f (-x)) :
    ∃ g : C(E, ℝ), ConvexOn ℝ univ g ∧ Integrable g γ ∧ (∀ x, 0 ≤ g x) ∧ g 0 = 0 ∧
      ∀ x ∈ F, ∫ y, g y ∂γ < g x := by
  let g : C(E, ℝ) := ⟨fun x => f x + f (-x) - 2 * f 0, by fun_prop⟩
  have hir : Integrable (fun x => f (-x)) γ := hn.integrable_comp_of_integrable hi
  have hmean : (∫ x, f (-x) ∂γ) = ∫ x, f x ∂γ := by
    calc
      _ = ∫ x, f x ∂(γ.map (fun x : E => -x)) :=
        (integral_map hn.measurable.aemeasurable f.continuous.aestronglyMeasurable).symm
      _ = _ := by rw [hn.map_eq]
  have hcneg : ConvexOn ℝ univ (fun x => f (-x)) := by
    simpa [Function.comp_def] using hcv.comp_linearMap (-(LinearMap.id : E →ₗ[ℝ] E))
  have hc : ConvexOn ℝ univ g := by
    change ConvexOn ℝ univ (fun x => f x + f (-x) - 2 * f 0)
    simpa only [sub_eq_add_neg, Pi.add_def] using (hcv.add hcneg).add_const (-(2 * f 0))
  have hgi : Integrable g γ := (hi.add hir).sub (integrable_const _)
  have hgm : (∫ x, g x ∂γ) = 2 * (∫ x, f x ∂γ) - 2 * f 0 := by
    change (∫ x, (f x + f (-x)) - 2 * f 0 ∂γ) = _
    have hsum : Integrable (fun x => f x + f (-x)) γ := hi.add hir
    rw [integral_sub hsum (integrable_const _), integral_add hi hir, hmean]
    simp [two_mul]
  refine ⟨g, hc, hgi, ?_, ?_, ?_⟩
  · intro x
    have hj : f ((1/2:ℝ) • x + (1/2:ℝ) • (-x)) ≤ (1/2:ℝ) • f x + (1/2:ℝ) • f (-x) :=
      hcv.2 (mem_univ x) (mem_univ (-x)) (by norm_num) (by norm_num) (by norm_num)
    simp only [smul_neg, add_neg_cancel, smul_eq_mul] at hj
    change 0 ≤ f x + f (-x) - 2 * f 0
    linarith
  · change f 0 + f (-0) - 2 * f 0 = 0
    simp [two_mul]
  · intro x hx
    rw [hgm]
    change _ < f x + f (-x) - 2 * f 0
    linarith [hp x hx, hm x hx]

private theorem finite_reflection (I : Finset ℕ) : MeasurePreserving (fun x : I → ℝ => -x)
    (Measure.pi (fun _ : I => gaussianReal 0 1)) (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
  refine ⟨measurable_neg, ?_⟩
  change (Measure.pi (fun _ : I => gaussianReal 0 1)).map (fun x i => -x i) = _
  have h (i : I) : AEMeasurable (fun y : ℝ => -y) (gaussianReal 0 1) := measurable_neg.aemeasurable
  rw [Measure.pi_map_pi h]
  simp [gaussianReal_map_neg]

/-- For a symmetric input and symmetric reference measure, triple decomposition and
Markov alone give a half-mass convex witness inside the doubled triple sum. -/
theorem symmetric_doubled_triple {ι : Type*} [Fintype ι] (γ : Measure (ι → ℝ)) [IsProbabilityMeasure γ]
    (hn : MeasurePreserving (fun x : ι → ℝ => -x) γ γ) (ht : CompactTripleDecomposition γ)
    {A : Set (ι → ℝ)} (hA : IsCompact A) (hneg : ∀ x ∈ A, -x ∈ A) (hm : 2 / 3 < γ.real A) :
    ∃ C : Set (ι → ℝ), IsCompact C ∧ Convex ℝ C ∧ C ⊆ (2 : ℝ) • (A + A + A) ∧
      (1 / 2 : ℝ≥0∞) ≤ γ C := by
  let D := A + A + A
  have hDn : ∀ x ∈ D, -x ∈ D := by
    rintro _ ⟨y, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩
    simpa [D, neg_add, add_comm, add_left_comm, add_assoc] using
      add_mem_add (add_mem_add (hneg a ha) (hneg b hb)) (hneg c hc)
  apply compact_core_of_avoidance γ (by norm_num) (IsCompact.smul (2 : ℝ) ((hA.add hA).add hA))
  intro F hF hdisj
  let H := (1 / 2 : ℝ) • F
  have hH : IsCompact H := IsCompact.smul (1/2 : ℝ) hF
  have hHD : Disjoint H D := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ hyd
    apply Set.disjoint_left.mp hdisj hx
    have h := Set.smul_mem_smul_set (a := (2 : ℝ)) hyd
    change x ∈ (2 : ℝ) • D
    change (2 : ℝ) • ((1/2 : ℝ) • x) ∈ (2 : ℝ) • D at h
    simpa only [smul_smul, show (2 : ℝ) * (1/2) = 1 by norm_num, one_smul] using h
  have hboth : Disjoint (H ∪ -H) D := by
    apply Set.disjoint_left.mpr
    rintro x (hx | hx) hxd
    · exact Set.disjoint_left.mp hHD hx hxd
    · exact Set.disjoint_left.mp hHD (Set.mem_neg.mp hx) (hDn _ hxd)
  obtain ⟨f, hf, hi, hsep⟩ := triple_sum_barrier γ ht hA.isClosed.measurableSet hm (hH.union hH.neg) hboth
  obtain ⟨g, hgc, hgi, hgn, hg0, hgap⟩ := even_barrier γ hn hf hi (F := H)
    (fun x hx => hsep x (Or.inl hx)) (fun x hx => hsep (-x) (Or.inr (Set.mem_neg.mpr (by simpa using hx))))
  let m := ∫ y, g y ∂γ
  refine ⟨{x | g x ≤ 2 * m}, isClosed_le g.continuous continuous_const, ?_, ?_,
    mass_at_twice_mean γ g.continuous.measurable hgn hgi⟩
  · simpa using hgc.convex_le (2 * m)
  · apply Set.disjoint_left.mpr
    intro x hx hs
    have hk := hgap ((1/2 : ℝ) • x) (Set.smul_mem_smul_set hx)
    have hj : g ((1/2 : ℝ) • x + (1/2 : ℝ) • 0) ≤ (1/2 : ℝ) • g x + (1/2 : ℝ) • g 0 :=
      hgc.2 (mem_univ x) (mem_univ 0) (by norm_num) (by norm_num) (by norm_num)
    simp only [smul_zero, add_zero, smul_eq_mul, hg0, mul_zero] at hj
    change m < g ((1/2 : ℝ) • x) at hk
    change g x ≤ 2 * m at hs
    linarith

#print axioms mass_at_twice_mean
#print axioms even_barrier
#print axioms symmetric_doubled_triple

omit [MeasurableSpace E] [BorelSpace E] in
private lemma doubled_subset_six (A : Set E) : (2 : ℝ) • (A + A + A) ⊆ (6 : ℕ) • A := by
  rintro _ ⟨x, hx, rfl⟩
  have h3 : x ∈ (3 : ℕ) • A := by simpa [succ_nsmul] using hx
  have hh := Set.nsmul_mem_nsmul (n := 2) h3
  rw [← mul_smul] at hh
  have he : (2 : ℝ) • x = (2 : ℕ) • x := by simpa using Nat.cast_smul_eq_nsmul ℝ 2 x
  change (2 : ℝ) • x ∈ (6 : ℕ) • A
  rw [he]
  exact hh

/-- Symmetrizing the input costs at most twice the missing mass. -/
theorem finite_six_of_triple (I : Finset ℕ) (hI : I.Nonempty) (ht : GaussianTripleDecomposition)
    {A : Set (I → ℝ)} (hA : IsCompact A) (hm : (5 / 6 : ℝ≥0∞) < finiteGaussian I A) :
    ∃ C : Set (I → ℝ), IsCompact C ∧ Convex ℝ C ∧ C ⊆ (6 : ℕ) • A ∧
      (1 / 2 : ℝ≥0∞) ≤ finiteGaussian I C := by
  let γ := finiteGaussian I
  let B := A ∩ -A
  have hB : IsCompact B := hA.inter_right hA.neg.isClosed
  have hn := finite_reflection I
  have hmirror : γ.real (-A) = γ.real A := hn.measureReal_preimage hA.isClosed.measurableSet.nullMeasurableSet
  have hsum := measureReal_union_add_inter (μ := γ) (s := A) hA.neg.isClosed.measurableSet
  rw [hmirror] at hsum
  have htotal : γ.real (A ∪ -A) ≤ 1 := by
    calc
      _ ≤ γ.real univ := measureReal_mono (subset_univ _)
      _ = 1 := probReal_univ
  have hmass : 5 / 6 < γ.real A := by
    have h := (ENNReal.toReal_lt_toReal (by finiteness) (measure_ne_top _ _)).mpr hm
    simpa [γ, Measure.real, ENNReal.toReal_div] using h
  have hlarge : 2 / 3 < γ.real B := by dsimp [B]; linarith
  have hBn (x) (hx : x ∈ B) : -x ∈ B := ⟨Set.mem_neg.mp hx.2, Set.mem_neg.mpr (by simpa using hx.1)⟩
  obtain ⟨C, hc, hv, hs, hμ⟩ := symmetric_doubled_triple γ hn (ht I hI) hB hBn hlarge
  have hsub : B ⊆ A := inter_subset_left
  exact ⟨C, hc, hv, hs.trans ((smul_set_mono (add_subset_add (add_subset_add hsub hsub) hsub)).trans
    (doubled_subset_six A)), hμ⟩

open Green54Projections
open scoped NNReal

/-- Coordinate projections preserve symmetry, so the countable symmetric input
retains the lower threshold of two thirds and the real dilation of its triple sum. -/
theorem gaussian_symmetric_of_triple (ht : GaussianTripleDecomposition) {K : Set Space}
    (hK : IsCompact K) (hn : ∀ x ∈ K, -x ∈ K) (hm : (2 / 3 : ℝ≥0∞) < gaussian K) :
    ∃ C : Set Space, IsCompact C ∧ Convex ℝ C ∧ C ⊆ (2 : ℝ) • (K + K + K) ∧
      (1 / 2 : ℝ≥0∞) ≤ gaussian C := by
  apply (compact_convex_iff_projections gaussian (IsCompact.smul (2 : ℝ) ((hK.add hK).add hK)) _).2
  intro I hI
  let p : Space →ₗ[ℝ] (I → ℝ) :=
    { toFun := I.restrict, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let A := I.restrict '' K
  have hA : IsCompact A := hK.image I.continuous_restrict
  have hAn (x) (hx : x ∈ A) : -x ∈ A := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨-y, hn y hy, rfl⟩
  have marginal : gaussian.map I.restrict = finiteGaussian I := Measure.infinitePi_map_restrict _
  have ha : gaussian K ≤ (finiteGaussian I) A := by
    rw [← marginal, Measure.map_apply I.continuous_restrict.measurable hA.isClosed.measurableSet]
    exact measure_mono fun x hx => ⟨x, hx, rfl⟩
  have hr := (ENNReal.toReal_lt_toReal (by finiteness) (measure_ne_top _ _)).mpr (hm.trans_le ha)
  obtain ⟨C, hc, hv, hs, hμ⟩ := symmetric_doubled_triple (finiteGaussian I) (finite_reflection I)
    (ht I hI) hA hAn (by simpa [Measure.real, ENNReal.toReal_div] using hr)
  refine ⟨C, hc, hv, ?_, marginal.symm ▸ hμ⟩
  rw [image_smul_comm I.restrict _ _ (fun _ => rfl)]
  change C ⊆ (2 : ℝ) • (p '' (K + K + K))
  rw [Set.image_add, Set.image_add]
  exact hs

/-- In the countable Gaussian product, triple decomposition alone yields six summands
and half the mass at input mass greater than five sixths. -/
theorem gaussian_six_of_triple (ht : GaussianTripleDecomposition) {K : Set Space}
    (hK : IsCompact K) (hμ : (5 / 6 : ℝ≥0∞) < gaussian K) :
    ∃ C : Set Space, IsCompact C ∧ Convex ℝ C ∧ C ⊆ (6 : ℕ) • K ∧
      (1 / 2 : ℝ≥0∞) ≤ gaussian C :=
  gaussian_sum_of_finite 6 (5 / 6) (1 / 2) (fun I hI _ => finite_six_of_triple I hI ht) hK hμ

/-- Exact positive pinned Green 54 declaration with the three-Gaussian theorem as its
only outstanding analytic input. -/
theorem green_54_of_triple (ht : GaussianTripleDecomposition) :
    ∀ K : Set (ℕ → ℝ), IsCompact K → Balanced ℝ K → (0.99 : ℝ≥0∞) ≤ gaussian K →
    ∃ C : Set (ℕ → ℝ), IsCompact C ∧ Convex ℝ C ∧ C ⊆ (10 : ℕ) • K ∧
      (0.01 : ℝ≥0∞) ≤ gaussian C := by
  intro K hK hb hμ
  have hl : (5 / 6 : ℝ≥0∞) < 0.99 := by
    change 5 / 6 < ((0.99 : ℝ≥0) : ℝ≥0∞)
    rw [← ENNReal.toReal_lt_toReal (by finiteness) ENNReal.coe_ne_top, ENNReal.coe_toReal]
    norm_num [ENNReal.toReal_div]
  have hs : (0.01 : ℝ≥0∞) ≤ 1 / 2 := by
    change ((0.01 : ℝ≥0) : ℝ≥0∞) ≤ 1 / 2
    rw [← ENNReal.toReal_le_toReal ENNReal.coe_ne_top (by finiteness), ENNReal.coe_toReal]
    norm_num [ENNReal.toReal_div]
  obtain ⟨C, hc, hv, hsub, hmass⟩ := gaussian_six_of_triple ht hK (hl.trans_le hμ)
  have hz := hb.zero_mem (nonempty_of_measure_ne_zero (s := K) (bot_le.trans_lt (hl.trans_le hμ)).ne')
  refine ⟨C, hc, hv, ?_, hs.trans hmass⟩
  intro x hx
  rw [show (10 : ℕ) = 6 + 4 by decide, add_nsmul]
  simpa using Set.add_mem_add (hsub hx) (Set.nsmul_mem_nsmul (n := 4) hz)

#print axioms finite_six_of_triple
#print axioms gaussian_symmetric_of_triple
#print axioms gaussian_six_of_triple
#print axioms green_54_of_triple

end Green54Symmetric
