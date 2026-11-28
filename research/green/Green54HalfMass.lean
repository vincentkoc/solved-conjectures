import Green54GaussianKernel
import Green54RectangularImages
import Green54GeneralLaws
import Mathlib.Tactic
/-! Gaussian measure amplification for compact balanced sets of mass at least one half. -/
open Set MeasureTheory ProbabilityTheory Real Green54GaussianKernel
open scoped ENNReal Pointwise RealInnerProductSpace
namespace Green54HalfMass
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

private theorem shift_density (v x : E) (hv : ‖v‖ ≤ 1/2) :
    (3/2 : ℝ) * gaussianDensity (0:E) 1 x ≤ gaussianDensity v 1 x + gaussianDensity (-v) 1 x := by
  let a := -‖x‖^2 / 2
  let b := -‖v‖^2 / 2
  let t := ⟪x,v⟫
  have h₁ : -‖x-v‖^2 / 2 = (a+b)+t := by
    simp only [a,b,t,norm_sub_sq_real]
    ring
  have h₂ : -‖x-(-v)‖^2 / 2 = (a+b)-t := by
    simp only [a,b,t,sub_neg_eq_add,norm_add_sq_real]
    ring
  have hb : 3/4 ≤ Real.exp b := by
    have h := Real.add_one_le_exp b
    dsimp [b] at *
    nlinarith [norm_nonneg v]
  have ht : 2 ≤ Real.exp t + Real.exp (-t) := by
    linarith [Real.add_one_le_exp t,Real.add_one_le_exp (-t)]
  simp only [gaussianDensity,NNReal.coe_one,mul_one,sub_zero,h₁,h₂]
  rw [show -‖x‖^2 / 2 = a from rfl,sub_eq_add_neg (a+b) t,Real.exp_add (a+b) t,
    Real.exp_add (a+b) (-t),Real.exp_add a b]
  let D := (Real.sqrt (2*Real.pi))⁻¹ ^ Fintype.card ι * Real.exp a
  have hD : 0 ≤ D := by dsimp [D]; positivity
  calc
    _ ≤ D * (Real.exp b * (Real.exp t + Real.exp (-t))) := by
      have hh : 3/2 ≤ Real.exp b * (Real.exp t + Real.exp (-t)) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr ht)]
      simpa only [D,mul_comm (3/2 : ℝ)] using mul_le_mul_of_nonneg_left hh hD
    _ = _ := by dsimp [D]; ring

/-- The two opposite translates have combined measure at least three halves of the input
measure when the translation vector has norm at most one half. -/
theorem opposite_shifts (v : E) (hv : ‖v‖ ≤ 1/2) {A : Set E} (hA : MeasurableSet A) :
    (3/2 : ℝ≥0∞) * stdGaussian E A ≤
      stdGaussian E ((fun x => v+x) ⁻¹' A) + stdGaussian E ((fun x => -v+x) ⁻¹' A) := by
  let d (m x : E) := ENNReal.ofReal (gaussianDensity m 1 x)
  have hm (m : E) : Measurable (d m) := by unfold d gaussianDensity; fun_prop
  have hd (m : E) : stdGaussian E ((fun x => m+x) ⁻¹' A) = ∫⁻ x in A, d m x := by
    have h := affine_gaussian_density m 1 one_ne_zero
    simp only [one_smul,one_pow] at h
    have hm' : Measurable (fun x : E => m+x) := by fun_prop
    rw [← Measure.map_apply hm' hA,h,withDensity_apply _ hA]
    rfl
  have h0 := hd (0:E)
  simp only [zero_add] at h0
  change stdGaussian E A = _ at h0
  rw [h0,hd v,hd (-v),← lintegral_add_left (hm v),← lintegral_const_mul _ (hm 0)]
  apply lintegral_mono
  intro x
  have hn (v : E) : 0 ≤ gaussianDensity v 1 x := by unfold gaussianDensity; positivity
  have hh := ENNReal.ofReal_le_ofReal (shift_density v x hv)
  rw [ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_add (hn v) (hn (-v))] at hh
  dsimp [d]
  norm_num [ENNReal.ofReal_div_of_pos] at hh ⊢
  exact hh

#print axioms opposite_shifts

/-- A balanced set of Gaussian mass at least one half has a twofold sum containing a
Euclidean ball with a dimension-independent radius. -/
theorem ball_in_two {A : Set E} (hA : MeasurableSet A) (ha : Balanced ℝ A)
    (hlarge : (1/2 : ℝ≥0∞) ≤ stdGaussian E A) :
    Metric.closedBall (0:E) (1/2) ⊆ A+A := by
  intro v hv
  have hn : ‖v‖ ≤ 1/2 := by simpa [Metric.mem_closedBall] using hv
  by_contra hbad
  let P := (fun x : E => v+x) ⁻¹' A
  let Q := (fun x : E => -v+x) ⁻¹' A
  have hP : MeasurableSet P := hA.preimage (by fun_prop)
  have hQ : MeasurableSet Q := hA.preimage (by fun_prop)
  have diff {x y : E} (hx : x ∈ A) (hy : y ∈ A) : x-y ∈ A+A :=
    ⟨x,hx,-y,ha.neg_mem_iff.mpr hy,by rw [sub_eq_add_neg]⟩
  have dAP : Disjoint A P := Set.disjoint_left.mpr fun x hx hp =>
    hbad (by simpa using diff (x := v+x) hp hx)
  have dAQ : Disjoint A Q := Set.disjoint_left.mpr fun x hx hq =>
    hbad (by simpa using diff hx (y := -v+x) hq)
  have dPQ : Disjoint P Q := by
    apply Set.disjoint_left.mpr
    intro x hp hq
    have half {z : E} (hz : z ∈ A) : (1/2 : ℝ) • z ∈ A :=
      balanced_iff_smul_mem.mp ha (by norm_num) hz
    apply hbad
    convert diff (half (z := v+x) hp) (half (z := -v+x) hq) using 1
    module
  have hu : stdGaussian E A + (stdGaussian E P + stdGaussian E Q) =
      stdGaussian E (A ∪ (P ∪ Q)) := by
    rw [measure_union (disjoint_union_right.mpr ⟨dAP,dAQ⟩) (hP.union hQ),measure_union dPQ hQ]
  apply (not_lt_of_ge (prob_le_one : stdGaussian E (A ∪ (P ∪ Q)) ≤ 1))
  calc
    (1 : ℝ≥0∞) < 1/2 + (3/2)*(1/2) := by
      apply (ENNReal.toReal_lt_toReal (by norm_num) (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul]
      norm_num [ENNReal.toReal_div]
    _ ≤ stdGaussian E A + (3/2)*stdGaussian E A := by gcongr
    _ ≤ stdGaussian E A + (stdGaussian E P + stdGaussian E Q) :=
      add_le_add le_rfl (opposite_shifts v hn hA)
    _ = _ := hu

#print axioms ball_in_two

private abbrev W := EuclideanSpace ℝ Unit

/-- The centered absolute first moment of a real-valued one-Lipschitz function is
bounded by a one-dimensional Gaussian constant in every input dimension. -/
theorem lipschitz_deviation (f : E → ℝ) (hf : LipschitzWith 1 f) :
    (∫ x, |f x - ∫ y, f y ∂stdGaussian E| ∂stdGaussian E) ≤
      2 * ∫ z : W, ‖z‖ ∂stdGaussian W := by
  let u : W := EuclideanSpace.single () 1
  have hu : ‖u‖ = 1 := by simp [u]
  let T (x : E) := f x • u
  have hT : LipschitzWith 2 T := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm]
    simp only [T,← sub_smul,norm_smul,hu,mul_one]
    have h := hf.dist_le_mul x y
    rw [Real.dist_eq] at h
    simp only [NNReal.coe_one,one_mul] at h
    change |f x-f y| ≤ 2 * dist x y
    linarith [show 0 ≤ dist x y from dist_nonneg]
  obtain ⟨ρ,h₁,h₂,hs⟩ := Green54RectangularImages.rectangular_sum hT
  let μ := (ρ : Measure (W × W))
  have m₁ : MeasurePreserving Prod.fst μ (stdGaussian W) := ⟨measurable_fst,h₁⟩
  have m₂ : MeasurePreserving Prod.snd μ (stdGaussian W) := ⟨measurable_snd,h₂⟩
  have hi : Integrable id (stdGaussian W) := IsGaussian.integrable_id
  have i₁ : Integrable Prod.fst μ := m₁.integrable_comp_of_integrable hi
  have i₂ : Integrable Prod.snd μ := m₂.integrable_comp_of_integrable hi
  calc
    _ = ∫ z, ‖z‖ ∂(stdGaussian E).map (fun x => T x - ∫ y, T y ∂stdGaussian E) := by
      have hm : Measurable (fun x : E => T x - ∫ y, T y ∂stdGaussian E) := hT.continuous.measurable.sub measurable_const
      rw [integral_map hm.aemeasurable continuous_norm.aestronglyMeasurable]
      simp only [T,integral_smul_const,← sub_smul,norm_smul,hu,mul_one,Real.norm_eq_abs]
    _ = ∫ z, ‖z.1+z.2‖ ∂μ := by
      have hm : Measurable (fun z : W × W => z.1+z.2) := by fun_prop
      rw [← hs,integral_map hm.aemeasurable continuous_norm.aestronglyMeasurable]
    _ ≤ ∫ z, ‖z.1‖+‖z.2‖ ∂μ :=
      integral_mono (i₁.add i₂).norm (i₁.norm.add i₂.norm) (fun z => norm_add_le _ _)
    _ = _ := by
      rw [integral_add i₁.norm i₂.norm,two_mul]
      congr 1
      · rw [← h₁,integral_map measurable_fst.aemeasurable continuous_norm.aestronglyMeasurable]
      · rw [← h₂,integral_map measurable_snd.aemeasurable continuous_norm.aestronglyMeasurable]

#print axioms lipschitz_deviation

/-- Expected norm of a one-dimensional standard Gaussian. -/
noncomputable def gaussianMeanNorm := ∫ z : W, ‖z‖ ∂stdGaussian W

/-- A single radius, independent of dimension, suffices to put more than two thirds
of the Gaussian mass within that distance of every half-mass compact set containing zero. -/
theorem large_neighborhood {A : Set E} (hA : MeasurableSet A) (hz : (0:E) ∈ A)
    (hlarge : 1/2 ≤ (stdGaussian E).real A) :
    2/3 < (stdGaussian E).real {x | Metric.infDist x A < 16*(gaussianMeanNorm+1)} := by
  let γ := stdGaussian E
  let f (x : E) := Metric.infDist x A
  let m := ∫ x, f x ∂γ
  have hl : LipschitzWith 1 f := Metric.lipschitz_infDist_pt A
  have hi : Integrable f γ := (IsGaussian.integrable_id (μ := γ)).norm.mono'
    hl.continuous.aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg Metric.infDist_nonneg]
      simpa using Metric.infDist_le_dist_of_mem (x := x) hz)
  have hm : 0 ≤ m := integral_nonneg fun _ => Metric.infDist_nonneg
  have hd : (∫ x, |f x-m| ∂γ) ≤ 2*gaussianMeanNorm := lipschitz_deviation f hl
  have he : γ.real A * m ≤ 2*gaussianMeanNorm := calc
    _ = ∫ _ in A, m ∂γ := by simp [smul_eq_mul]
    _ = ∫ x in A, |f x - m| ∂γ := by
      apply setIntegral_congr_fun hA
      intro x hx
      simp [f,Metric.infDist_zero_of_mem hx,abs_of_nonneg hm]
    _ ≤ ∫ x, |f x-m| ∂γ := setIntegral_le_integral (hi.sub (integrable_const m)).abs
      (ae_of_all _ fun x => abs_nonneg _)
    _ ≤ _ := hd
  have hmean : m ≤ 4*gaussianMeanNorm := by
    change 1/2 ≤ γ.real A at hlarge
    nlinarith [mul_nonneg (sub_nonneg.mpr hlarge) hm]
  let R := 16*(gaussianMeanNorm+1)
  have hM : 0 ≤ gaussianMeanNorm := integral_nonneg fun _ => norm_nonneg _
  have hR : 0 < R := by dsimp [R]; linarith
  let B := {x | R ≤ f x}
  have hB : MeasurableSet B := measurableSet_le measurable_const hl.continuous.measurable
  have hmark : R * γ.real B ≤ m := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ fun x => Metric.infDist_nonneg) hi R
  have hbad : γ.real B < 1/3 := by
    by_contra! hc
    have h := mul_nonneg hR.le (sub_nonneg.mpr hc)
    dsimp [R] at hmark h
    nlinarith
  have hcom : {x | f x < R} = Bᶜ := by ext; simp [B]
  change 2/3 < γ.real {x | f x < R}
  rw [hcom,measureReal_compl hB,probReal_univ]
  linarith

#print axioms large_neighborhood

private theorem compact_sum {V : Type*} [NormedAddCommGroup V] {A : Set V} (hA : IsCompact A)
    (n : ℕ) : IsCompact (n • A) := by
  induction n with
  | zero => simp
  | succ n ih => simpa [succ_nsmul] using ih.add hA

private theorem expand (N : ℕ) (hN : 32 * (gaussianMeanNorm + 1) < N) {A : Set E}
    (hA : IsCompact A) (ha : Balanced ℝ A) (hlarge : (1/2 : ℝ≥0∞) ≤ stdGaussian E A) :
    2/3 < (stdGaussian E).real ((2*N+1) • A) := by
  have hM : 0 ≤ gaussianMeanNorm := integral_nonneg fun _ => norm_nonneg _
  have hp : (0:ℝ) < N := by linarith
  have hne : A.Nonempty := by
    by_contra! hz
    simp [hz] at hlarge
  have hz := ha.zero_mem hne
  have hr : (1/2:ℝ) ≤ (stdGaussian E).real A := by
    have h := ENNReal.toReal_mono (measure_ne_top _ _) hlarge
    simpa [Measure.real,ENNReal.toReal_div] using h
  apply (large_neighborhood hA.measurableSet hz hr).trans_le
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  obtain ⟨y,hy,hd⟩ := hA.exists_infDist_eq_dist hne x
  let v := (N:ℝ)⁻¹ • (x-y)
  have hv : v ∈ Metric.closedBall (0:E) (1/2) := by
    rw [Metric.mem_closedBall,dist_zero_right]
    dsimp [v]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp),← div_eq_inv_mul,← dist_eq_norm,← hd]
    apply (div_le_iff₀ hp).mpr
    change Metric.infDist x A < 16*(gaussianMeanNorm+1) at hx
    linarith
  have ht : v ∈ (2:ℕ) • A := by
    simpa [two_nsmul] using ball_in_two hA.measurableSet ha hlarge hv
  have hs := Set.nsmul_mem_nsmul (n := N) ht
  have he : N • v = x-y := by
    rw [← Nat.cast_smul_eq_nsmul ℝ N v]
    simp [v,smul_smul,hp.ne']
  rw [he,← mul_smul] at hs
  rw [Nat.mul_comm] at hs
  rw [succ_nsmul]
  exact ⟨x-y,hs,y,hy,sub_add_cancel x y⟩

/-- One number of Minkowski summands works in every dimension, even at the
closed input threshold of one half of the Gaussian mass. -/
theorem half_mass_convexity :
    ∃ q : ℕ, 0 < q ∧ ∀ (ι : Type) [Fintype ι], ∀ A : Set (ι → ℝ), IsCompact A →
      Balanced ℝ A → (1/2 : ℝ≥0∞) ≤ Measure.pi (fun _ : ι => gaussianReal 0 1) A →
      ∃ C : Set (ι → ℝ), IsCompact C ∧ Convex ℝ C ∧ C ⊆ q • A ∧
        (1/2 : ℝ≥0∞) ≤ Measure.pi (fun _ : ι => gaussianReal 0 1) C := by
  classical
  obtain ⟨N,hN⟩ := exists_nat_gt (32*(gaussianMeanNorm+1))
  let k := 2*N+1
  refine ⟨6*k,by dsimp [k]; positivity,?_⟩
  intro I _ A hA ha hlarge
  let γ := Measure.pi (fun _ : I => gaussianReal 0 1)
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ)).symm
  let B := L '' A
  have hB : IsCompact B := hA.image L.continuous
  have hb : Balanced ℝ B := by
    apply balanced_iff_smul_mem.mpr
    rintro s hs _ ⟨x,hx,rfl⟩
    exact ⟨s • x,ha.smul_mem hs hx,map_smul L s x⟩
  have mp : γ.map L = stdGaussian (EuclideanSpace ℝ I) := map_pi_eq_stdGaussian
  have mass (S : Set (I → ℝ)) (hS : IsCompact S) :
      stdGaussian (EuclideanSpace ℝ I) (L '' S) = γ S := by
    rw [← mp,Measure.map_apply L.continuous.measurable (hS.image L.continuous).measurableSet]
    rw [preimage_image_eq _ L.injective]
  have hx := expand N hN hB hb ((mass A hA).symm ▸ hlarge)
  change 2/3 < ((stdGaussian (EuclideanSpace ℝ I)) (k • (L '' A))).toReal at hx
  rw [← Set.image_nsmul L A k,mass _ (compact_sum hA k)] at hx
  have bh (n : ℕ) : Balanced ℝ (n • A) := by
    induction n with
    | zero => simpa only [zero_smul] using (balanced_zero : Balanced ℝ (0 : Set (I → ℝ)))
    | succ n ih => simpa [succ_nsmul] using ih.add ha
  have hn : MeasurePreserving (fun x : I → ℝ => -x) γ γ := by
    refine ⟨measurable_neg,?_⟩
    change (Measure.pi (fun _ : I => gaussianReal 0 1)).map (fun x i => -x i) = _
    have hm (i : I) : AEMeasurable (fun y : ℝ => -y) (gaussianReal 0 1) := measurable_neg.aemeasurable
    rw [Measure.pi_map_pi hm]
    simp [γ,gaussianReal_map_neg]
  have ht : Green54ConvexTests.CompactTripleDecomposition γ := by
    intro F _ ν hν
    exact Green54GeneralLaws.gaussian_triple_fintype I (ν.map measurable_subtype_coe.aemeasurable) hν
  obtain ⟨C,hc,hv,hsub,hμ⟩ := Green54Symmetric.symmetric_doubled_triple γ hn ht (compact_sum hA k)
    (fun _ hx => (bh k).neg_mem_iff.mpr hx) hx
  refine ⟨C,hc,hv,hsub.trans ?_,hμ⟩
  rintro _ ⟨y,hy,rfl⟩
  have h3 : y ∈ (3:ℕ) • (k • A) := by simpa [succ_nsmul] using hy
  have h2 := Set.nsmul_mem_nsmul (n := 2) h3
  rw [← mul_smul,← mul_smul] at h2
  change (2:ℝ) • y ∈ ((2*3)*k) • A
  convert h2 using 1
  exact Nat.cast_smul_eq_nsmul ℝ 2 y

#print axioms half_mass_convexity

/-- Talagrand's half-mass formulation with the quantifiers of the proposed DeepMind declaration. -/
theorem talagrand_convexity_problem :
    ∃ q : ℕ, 0 < q ∧ ∀ n : ℕ, 0 < n → ∀ A : Set (Fin n → ℝ), IsCompact A →
      Balanced ℝ A → (1/2 : ℝ≥0∞) ≤ Measure.pi (fun _ : Fin n => gaussianReal 0 1) A →
      ∃ C : Set (Fin n → ℝ), IsCompact C ∧ Convex ℝ C ∧ C ⊆ q • A ∧
        (1/2 : ℝ≥0∞) ≤ Measure.pi (fun _ : Fin n => gaussianReal 0 1) C := by
  obtain ⟨q,hq,h⟩ := half_mass_convexity
  exact ⟨q,hq,fun n _ => h (Fin n)⟩

#print axioms talagrand_convexity_problem

end Green54HalfMass
