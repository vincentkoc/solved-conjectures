import Mathlib.Topology.Sets.VietorisTopology
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
import Mathlib.Tactic

/-! A compact convex subset of a compact set in a countable product can be detected
from its finite Gaussian marginals. -/

open Set Filter TopologicalSpace MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal Pointwise

namespace Green54Projections

abbrev Space := ℕ → ℝ

private abbrev proj (I : Finset ℕ) : Space → (I → ℝ) := I.restrict

private def projLinear (I : Finset ℕ) : Space →ₗ[ℝ] (I → ℝ) where
  toFun := proj I
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def trim {I J : Finset ℕ} (h : I ⊆ J) : (J → ℝ) →ₗ[ℝ] (I → ℝ) where
  toFun x i := x ⟨i.val, h i.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma image_trim {I J : Finset ℕ} (h : I ⊆ J) (K : Set Space) :
    (trim h) '' (proj J '' K) = proj I '' K := by rw [image_image]; rfl

private def shadow (I : Finset ℕ) (K : Set Space) := proj I ⁻¹' (proj I '' K)

private lemma shadow_antitone (K : Set Space) : Antitone (fun I => shadow I K) := by
  intro I J hij x hx
  obtain ⟨y, hy, he⟩ := hx
  exact ⟨y, hy, congrArg (trim hij) he⟩

private lemma shadow_eq {K : Set Space} (hK : IsCompact K) : (⋂ I, shadow I K) = K := by
  have hs : K ⊆ ⋂ I, shadow I K := by
    apply subset_iInter
    intro I x hx
    exact ⟨x, hx, rfl⟩
  apply Subset.antisymm _ hs
  intro x hx
  let F (I : Finset ℕ) := K ∩ (proj I ⁻¹' {proj I x})
  have hclosed (I : Finset ℕ) : IsClosed (F I) :=
    hK.isClosed.inter (isClosed_singleton.preimage I.continuous_restrict)
  have hmono : Antitone F := by
    intro I J hij y hy
    exact ⟨hy.1, congrArg (trim hij) (show proj J y = proj J x from hy.2)⟩
  have hne (I : Finset ℕ) : (F I).Nonempty := by
    obtain ⟨y, hy, he⟩ := mem_iInter.mp hx I
    exact ⟨y, hy, he⟩
  obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed F
    hmono.directed_ge hne (fun I => hK.of_isClosed_subset (hclosed I) inter_subset_left) hclosed
  have he : y = x := by
    funext i
    have hj : proj {i} y = proj {i} x := (mem_iInter.mp hy {i}).2
    exact congrFun hj ⟨i, Finset.mem_singleton_self i⟩
  exact he ▸ (mem_iInter.mp hy ∅).1

private lemma convex_closed {ι : Type*} :
    IsClosed {K : Compacts (ι → ℝ) | Convex ℝ (K : Set (ι → ℝ))} := by
  let W := {w : ℝ × ℝ // 0 ≤ w.1 ∧ 0 ≤ w.2 ∧ w.1 + w.2 = 1}
  let f (w : W) (p : (ι → ℝ) × (ι → ℝ)) := w.val.1 • p.1 + w.val.2 • p.2
  have hf (w : W) : Continuous (f w) := by dsimp [f]; fun_prop
  let mix (w : W) (K : Compacts (ι → ℝ)) := (K ×ˢ K).map (f w) (hf w)
  have hm (w : W) : Continuous (mix w) :=
    (hf w).compacts_map.comp (Compacts.continuous_prod.comp (continuous_id.prodMk continuous_id))
  have he : {K : Compacts (ι → ℝ) | Convex ℝ (K : Set (ι → ℝ))} =
      ⋂ w : W, {K | mix w K ⊔ K = K} := by
    ext K
    simp only [mem_ofPred_eq, mem_iInter, sup_eq_right]
    constructor
    · intro h w z hz
      obtain ⟨⟨x, y⟩, hxy, rfl⟩ := hz
      exact h hxy.1 hxy.2 w.property.1 w.property.2.1 w.property.2.2
    · intro h x hx y hy a b ha hb hab
      exact h ⟨(a,b), ha, hb, hab⟩ (show f ⟨(a,b), ha, hb, hab⟩ (x,y) ∈
        mix ⟨(a,b), ha, hb, hab⟩ K from ⟨(x,y), ⟨hx, hy⟩, rfl⟩)
  rw [he]
  exact isClosed_iInter fun w => isClosed_eq ((hm w).sup continuous_id) continuous_id

private lemma mass_closed {ι : Type*} (ν : Measure (ι → ℝ)) [ν.OuterRegular] (β : ℝ≥0∞) :
    IsClosed {K : Compacts (ι → ℝ) | β ≤ ν (K : Set (ι → ℝ))} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro K hK
  obtain ⟨U, hKU, hU, hβ⟩ := Set.exists_isOpen_lt_of_lt (K : Set (ι → ℝ)) β (lt_of_not_ge hK)
  refine ⟨{L : Compacts (ι → ℝ) | (L : Set (ι → ℝ)) ⊆ U}, ?_,
    Compacts.isOpen_subsets_of_isOpen hU, hKU⟩
  exact fun L hL => not_le_of_gt ((measure_mono hL).trans_lt hβ)

private lemma map_mass (μ : Measure Space) (I : Finset ℕ) {K : Set Space} (hK : IsCompact K) :
    (μ.map (proj I)) (proj I '' K) = μ (shadow I K) :=
  Measure.map_apply I.continuous_restrict.measurable
    (hK.image I.continuous_restrict).isClosed.measurableSet

/-- Finite projections may choose their compact convex witnesses independently. -/
theorem compact_convex_iff_projections (μ : Measure Space) [IsFiniteMeasure μ]
    {D : Set Space} (hD : IsCompact D) (β : ℝ≥0∞) :
    (∃ C : Set Space, IsCompact C ∧ Convex ℝ C ∧ C ⊆ D ∧ β ≤ μ C) ↔
      ∀ I : Finset ℕ, I.Nonempty → ∃ L : Set (I → ℝ), IsCompact L ∧ Convex ℝ L ∧
        L ⊆ I.restrict '' D ∧ β ≤ (μ.map I.restrict) L := by
  classical
  constructor
  · rintro ⟨C, hc, hv, hsub, hm⟩ I _
    refine ⟨proj I '' C, hc.image I.continuous_restrict, hv.linear_image (projLinear I),
      image_mono hsub, ?_⟩
    rw [map_mass μ I hc]
    exact hm.trans (measure_mono fun x hx => ⟨x, hx, rfl⟩)
  intro H
  let good (I : Finset ℕ) : Set (Compacts Space) := {C | (C : Set Space) ⊆ D ∧
    Convex ℝ (proj I '' (C : Set Space)) ∧ β ≤ μ (shadow I (C : Set Space))}
  have closed (I : Finset ℕ) : IsClosed (good I) := by
    let f (C : Compacts Space) := C.map (proj I) I.continuous_restrict
    have hf : Continuous f := I.continuous_restrict.compacts_map
    have he : good I = {C : Compacts Space | (C : Set Space) ⊆ D} ∩
        f ⁻¹' ({L : Compacts (I → ℝ) | Convex ℝ (L : Set (I → ℝ))} ∩
          {L : Compacts (I → ℝ) | β ≤ (μ.map (proj I)) (L : Set (I → ℝ))}) := by
      ext C
      change (_ ∧ _ ∧ β ≤ μ (shadow I (C : Set Space))) ↔
        (_ ∧ _ ∧ β ≤ (μ.map (proj I)) (proj I '' (C : Set Space)))
      rw [map_mass μ I C.isCompact]
      rfl
    rw [he]
    exact (Compacts.isClosed_subsets_of_isClosed hD.isClosed).inter
      ((convex_closed.inter (mass_closed (μ.map (proj I)) β)).preimage hf)
  have mono : Antitone good := by
    intro I J hij C hC
    refine ⟨hC.1, ?_, hC.2.2.trans (measure_mono (shadow_antitone _ hij))⟩
    rw [← image_trim hij]
    exact hC.2.1.linear_image (trim hij)
  have compact (I : Finset ℕ) : IsCompact (good I) :=
    (Compacts.isCompact_subsets_of_isCompact hD).of_isClosed_subset (closed I) (fun _ h => h.1)
  have inhabited (I : Finset ℕ) (hI : I.Nonempty) : (good I).Nonempty := by
    obtain ⟨L, hL, hv, hsub, hm⟩ := H I hI
    let C : Compacts Space := ⟨D ∩ proj I ⁻¹' L, hD.inter_right
      (hL.isClosed.preimage I.continuous_restrict)⟩
    have he : proj I '' (C : Set Space) = L := by
      apply Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact hx.2
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := hsub hy
        exact ⟨x, ⟨hx, hy⟩, rfl⟩
    refine ⟨C, inter_subset_left, he.symm ▸ hv, ?_⟩
    rw [← map_mass μ I C.isCompact, he]
    exact hm
  have ne (I : Finset ℕ) : (good I).Nonempty :=
    (inhabited (insert 0 I) (Finset.insert_nonempty ..)).mono (mono (Finset.subset_insert ..))
  obtain ⟨C, hall⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    good mono.directed_ge ne compact closed
  have h (I : Finset ℕ) := mem_iInter.mp hall I
  refine ⟨C, C.isCompact, ?_, (h ∅).1, ?_⟩
  · rw [← shadow_eq C.isCompact]
    exact convex_iInter fun I => (h I).2.1.linear_preimage (projLinear I)
  · rw [← shadow_eq C.isCompact, (shadow_antitone (C : Set Space)).measure_iInter]
    · exact le_iInf fun I => (h I).2.2
    · intro I
      exact ((C.isCompact.image I.continuous_restrict).isClosed.preimage
        I.continuous_restrict).measurableSet.nullMeasurableSet
    · exact ⟨∅, measure_ne_top μ _⟩

/-- The Gaussian product used in the pinned DeepMind statement. -/
noncomputable abbrev gaussian := Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

/-- The compact-input consequence of Hua–Song–Tudose, Corollary 5.2, at b = c = 1/3. -/
def FiniteGaussianConvexity : Prop :=
  ∀ (I : Finset ℕ), I.Nonempty → ∀ A : Set (I → ℝ), IsCompact A →
    (5 / 6 : ℝ≥0∞) < (Measure.pi (fun _ : I => gaussianReal 0 1)) A →
    ∃ C : Set (I → ℝ), IsCompact C ∧ Convex ℝ C ∧ C ⊆ (3 : ℝ) • (A + A + A) ∧
      (1 / 3 : ℝ≥0∞) ≤ (Measure.pi (fun _ : I => gaussianReal 0 1)) C

private lemma project_dilation (I : Finset ℕ) (K : Set Space) :
    proj I '' ((3 : ℝ) • (K + K + K)) = (3 : ℝ) • (proj I '' K + proj I '' K + proj I '' K) := by
  rw [image_smul_comm (proj I) _ _ (fun _ => rfl)]
  change (3 : ℝ) • (projLinear I '' (K + K + K)) = _
  rw [Set.image_add, Set.image_add]
  rfl

/-- The finite analytic estimate passes to a countable product with its constants intact. -/
theorem gaussian_dilation_of_finite (hfinite : FiniteGaussianConvexity)
    {K : Set Space} (hK : IsCompact K) (hm : (5 / 6 : ℝ≥0∞) < gaussian K) :
    ∃ C : Set Space, IsCompact C ∧ Convex ℝ C ∧ C ⊆ (3 : ℝ) • (K + K + K) ∧
      (1 / 3 : ℝ≥0∞) ≤ gaussian C := by
  apply (compact_convex_iff_projections gaussian (IsCompact.smul (3 : ℝ) ((hK.add hK).add hK)) _).2
  intro I hI
  have marginal : gaussian.map (proj I) = Measure.pi (fun _ : I => gaussianReal 0 1) :=
    Measure.infinitePi_map_restrict _
  have hmass : gaussian K ≤ (gaussian.map (proj I)) (proj I '' K) := by
    rw [map_mass gaussian I hK]
    exact measure_mono fun x hx => ⟨x, hx, rfl⟩
  rw [marginal] at hmass
  obtain ⟨C, hc, hv, hs, hμ⟩ := hfinite I hI (proj I '' K) (hK.image I.continuous_restrict)
    (hm.trans_le hmass)
  refine ⟨C, hc, hv, ?_, marginal.symm ▸ hμ⟩
  exact (project_dilation I K).symm ▸ hs

/-- Conversely, compact approximation of a finite cylinder recovers the finite estimate. -/
theorem finite_iff_countable : FiniteGaussianConvexity ↔
    ∀ K : Set Space, IsCompact K → (5 / 6 : ℝ≥0∞) < gaussian K →
      ∃ C : Set Space, IsCompact C ∧ Convex ℝ C ∧ C ⊆ (3 : ℝ) • (K + K + K) ∧
        (1 / 3 : ℝ≥0∞) ≤ gaussian C := by
  refine ⟨fun H _ => gaussian_dilation_of_finite H, ?_⟩
  intro H I _ A hA hm
  have marginal : gaussian.map (proj I) = Measure.pi (fun _ : I => gaussianReal 0 1) :=
    Measure.infinitePi_map_restrict _
  rw [← marginal, Measure.map_apply I.continuous_restrict.measurable hA.isClosed.measurableSet] at hm
  obtain ⟨K, hsub, hK, hlarge⟩ := (hA.isClosed.preimage I.continuous_restrict).measurableSet
    |>.exists_lt_isCompact_of_ne_top (measure_ne_top gaussian _) hm
  obtain ⟨C, hc, hv, hs, hμ⟩ := H K hK hlarge
  refine ⟨proj I '' C, hc.image I.continuous_restrict, hv.linear_image (projLinear I), ?_, ?_⟩
  · have hp : proj I '' K ⊆ A := image_subset_iff.mpr hsub
    exact (image_mono hs).trans ((project_dilation I K).symm ▸
      smul_set_mono (add_subset_add (add_subset_add hp hp) hp))
  · rw [← marginal, map_mass gaussian I hc]
    exact hμ.trans (measure_mono fun x hx => ⟨x, hx, rfl⟩)

private lemma dilation_subset_nine (K : Set Space) :
    (3 : ℝ) • (K + K + K) ⊆ (9 : ℕ) • K := by
  rintro _ ⟨y, hy, rfl⟩
  have hy' : y ∈ (3 : ℕ) • K := by simpa [succ_nsmul] using hy
  have h := (Set.nsmul_mem_nsmul (n := 3) hy')
  rw [← mul_smul] at h
  have he : (3 : ℝ) • y = (3 : ℕ) • y := by simpa using Nat.cast_smul_eq_nsmul ℝ 3 y
  change (3 : ℝ) • y ∈ (9 : ℕ) • K
  rw [he]
  exact h

/-- Nine Minkowski summands suffice at mass greater than 5/6, conditional on the finite input. -/
theorem gaussian_nine_of_finite (hfinite : FiniteGaussianConvexity)
    {K : Set Space} (hK : IsCompact K) (hm : (5 / 6 : ℝ≥0∞) < gaussian K) :
    ∃ C : Set Space, IsCompact C ∧ Convex ℝ C ∧ C ⊆ (9 : ℕ) • K ∧
      (1 / 3 : ℝ≥0∞) ≤ gaussian C := by
  obtain ⟨C, hc, hv, hs, hμ⟩ := gaussian_dilation_of_finite hfinite hK hm
  exact ⟨C, hc, hv, hs.trans (dilation_subset_nine K), hμ⟩

/-- The positive Green 54 declaration, conditional only on the finite-dimensional input. -/
theorem green_54_of_finite (hfinite : FiniteGaussianConvexity) :
    ∀ K : Set (ℕ → ℝ), IsCompact K → Balanced ℝ K → (0.99 : ℝ≥0∞) ≤ gaussian K →
    ∃ C : Set (ℕ → ℝ), IsCompact C ∧ Convex ℝ C ∧ C ⊆ (10 : ℕ) • K ∧
      (0.01 : ℝ≥0∞) ≤ gaussian C := by
  intro K hK hb hμ
  have hlarge : (5 / 6 : ℝ≥0∞) < 0.99 := by
    change 5 / 6 < ((0.99 : ℝ≥0) : ℝ≥0∞)
    rw [← ENNReal.toReal_lt_toReal (by finiteness) ENNReal.coe_ne_top, ENNReal.coe_toReal]
    norm_num [ENNReal.toReal_div]
  have hsmall : (0.01 : ℝ≥0∞) ≤ 1 / 3 := by
    change ((0.01 : ℝ≥0) : ℝ≥0∞) ≤ 1 / 3
    rw [← ENNReal.toReal_le_toReal ENNReal.coe_ne_top (by finiteness), ENNReal.coe_toReal]
    norm_num [ENNReal.toReal_div]
  obtain ⟨C, hc, hv, hs, hm⟩ := gaussian_nine_of_finite hfinite hK (hlarge.trans_le hμ)
  have hz := hb.zero_mem (nonempty_of_measure_ne_zero (s := K)
    (bot_le.trans_lt (hlarge.trans_le hμ)).ne')
  refine ⟨C, hc, hv, hs.trans ?_, hsmall.trans hm⟩
  intro x hx
  rw [show (10 : ℕ) = 9 + 1 from rfl, succ_nsmul]
  simpa using Set.add_mem_add hx hz

#print axioms compact_convex_iff_projections
#print axioms gaussian_dilation_of_finite
#print axioms finite_iff_countable
#print axioms gaussian_nine_of_finite
#print axioms green_54_of_finite

end Green54Projections
