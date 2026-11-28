import Green54LipschitzImages

/-! Gaussian images between Euclidean spaces of different dimensions. -/

open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace Green54RectangularImages
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
local notation "V" => EuclideanSpace ℝ ι
local notation "W" => EuclideanSpace ℝ κ
local notation "H" => EuclideanSpace ℝ (ι ⊕ κ)

private def left (x : H) : V := WithLp.toLp 2 (fun i => x (Sum.inl i))

private def right (x : H) : W := WithLp.toLp 2 (fun i => x (Sum.inr i))

private def pad (x : W) : H := WithLp.toLp 2 (Sum.elim (fun _ => 0) (fun i => x i))

private theorem left_lip : LipschitzWith 1 (left (ι := ι) (κ := κ)) := by
  let e := PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2 (fun _ : ι ⊕ κ => ℝ)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul]
  change dist (e x).fst (e y).fst ≤ dist x y
  exact (WithLp.dist_fst_le (e x) (e y)).trans_eq (e.isometry.dist_eq x y)

private theorem pad_iso : Isometry (pad (ι := ι) (κ := κ)) := by
  apply Isometry.of_dist_eq
  intro x y
  let e := PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2 (fun _ : ι ⊕ κ => ℝ)
  rw [← e.isometry.dist_eq (pad x) (pad y)]
  change dist (WithLp.toLp 2 ((0 : V), x)) (WithLp.toLp 2 ((0 : V), y)) = _
  exact WithLp.dist_toLp_snd 2 V W x y

private theorem left_mp : MeasurePreserving (left (ι := ι) (κ := κ)) (stdGaussian H) (stdGaussian V) := by
  have hlm : Measurable (left (ι := ι) (κ := κ)) :=
    (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda _ fun i =>
      (EuclideanSpace.proj (Sum.inl i)).continuous.measurable)
  refine ⟨hlm,?_⟩
  rw [← map_pi_eq_stdGaussian, Measure.map_map hlm (PiLp.continuous_toLp 2 _).measurable]
  have hp := measurePreserving_fst.comp (measurePreserving_sumPiEquivProdPi
    (fun _ : ι ⊕ κ => gaussianReal 0 1))
  have hvec : MeasurePreserving (WithLp.toLp 2 : (ι → ℝ) → V)
      (Measure.pi fun _ => gaussianReal 0 1) (stdGaussian V) :=
    ⟨(PiLp.continuous_toLp 2 _).measurable, map_pi_eq_stdGaussian⟩
  exact (hvec.comp hp).map_eq

private theorem right_mp : MeasurePreserving (right (ι := ι) (κ := κ)) (stdGaussian H) (stdGaussian W) := by
  have hlm : Measurable (right (ι := ι) (κ := κ)) :=
    (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda _ fun i =>
      (EuclideanSpace.proj (Sum.inr i)).continuous.measurable)
  refine ⟨hlm,?_⟩
  rw [← map_pi_eq_stdGaussian, Measure.map_map hlm (PiLp.continuous_toLp 2 _).measurable]
  have hp := measurePreserving_snd.comp (measurePreserving_sumPiEquivProdPi
    (fun _ : ι ⊕ κ => gaussianReal 0 1))
  have hvec : MeasurePreserving (WithLp.toLp 2 : (κ → ℝ) → W)
      (Measure.pi fun _ => gaussianReal 0 1) (stdGaussian W) :=
    ⟨(PiLp.continuous_toLp 2 _).measurable, map_pi_eq_stdGaussian⟩
  exact (hvec.comp hp).map_eq

private def projectRight : H →L[ℝ] W :=
  LinearMap.mkContinuous
    { toFun := right
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 <| by
    intro x
    let e := PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2 (fun _ : ι ⊕ κ => ℝ)
    change ‖(e x).snd‖ ≤ 1 * ‖x‖
    rw [one_mul]
    exact (WithLp.norm_snd_le V (e x)).trans_eq (e.norm_map x)

private theorem gauss_int {i j : Type*} [Fintype i] [Fintype j] {T : EuclideanSpace ℝ i → EuclideanSpace ℝ j}
    (hT : LipschitzWith 2 T) : Integrable T (stdGaussian _) := by
  have hi := (IsGaussian.memLp_two_id (μ := stdGaussian (EuclideanSpace ℝ i))).norm.integrable (by norm_num)
  apply ((hi.const_mul 2).add (integrable_const ‖T 0‖)).mono' hT.continuous.aestronglyMeasurable
  apply ae_of_all
  intro z
  have hb := hT.norm_sub_le z 0
  simp only [sub_zero, NNReal.coe_ofNat] at hb
  change ‖T z‖ ≤ 2 * ‖z‖ + ‖T 0‖
  linarith [norm_sub_norm_le (T z) (T 0)]

/-- A 2-Lipschitz image of any finite-dimensional standard Gaussian, after centering,
is a sum of two standard Gaussians in the output space. -/
theorem rectangular_sum {T : V → W} (hT : LipschitzWith 2 T) :
    ∃ ρ : ProbabilityMeasure (W × W), (ρ : Measure (W × W)).map Prod.fst = stdGaussian W ∧
      (ρ : Measure (W × W)).map Prod.snd = stdGaussian W ∧
      (ρ : Measure (W × W)).map (fun z => z.1 + z.2) =
        (stdGaussian V).map (fun g => T g - ∫ w, T w ∂stdGaussian V) := by
  let L := left (ι := ι) (κ := κ)
  let R := projectRight (ι := ι) (κ := κ)
  let Φ (x : H) := pad (ι := ι) (T (L x))
  have hΦ : LipschitzWith 2 Φ := by simpa [Φ,L,Function.comp_def] using
    ((pad_iso (ι := ι) (κ := κ)).lipschitz.comp (hT.comp (left_lip (ι := ι) (κ := κ))))
  have hpL : MeasurePreserving L (stdGaussian H) (stdGaussian V) := left_mp
  have hpR : MeasurePreserving R (stdGaussian H) (stdGaussian W) := right_mp
  obtain ⟨ρ,h₁,h₂,hs⟩ := Green54LipschitzImages.centered_lipschitz_sum hΦ
  let p (z : H × H) := (R z.1,R z.2)
  have hm : Measurable p := (R.measurable.comp measurable_fst).prodMk (R.measurable.comp measurable_snd)
  refine ⟨ρ.map hm.aemeasurable,?_,?_,?_⟩
  · change ((ρ : Measure (H × H)).map p).map Prod.fst = _
    rw [Measure.map_map measurable_fst hm]
    exact ((Measure.map_map R.measurable measurable_fst).symm.trans (congrArg (Measure.map R) h₁)).trans hpR.map_eq
  · change ((ρ : Measure (H × H)).map p).map Prod.snd = _
    rw [Measure.map_map measurable_snd hm]
    exact ((Measure.map_map R.measurable measurable_snd).symm.trans (congrArg (Measure.map R) h₂)).trans hpR.map_eq
  · have hRΦ (x : H) : R (Φ x) = T (L x) := rfl
    have hμ : R (∫ h, Φ h ∂stdGaussian H) = ∫ g, T g ∂stdGaussian V := by
      rw [← R.integral_comp_comm (gauss_int hΦ)]
      simp only [hRΦ]
      rw [← hpL.map_eq, integral_map hpL.measurable.aemeasurable hT.continuous.aestronglyMeasurable]
    let M (x : V) := T x - ∫ g, T g ∂stdGaussian V
    have hM : Measurable M := hT.continuous.measurable.sub measurable_const
    have hΦm : Measurable (fun g => Φ g - ∫ w, Φ w ∂stdGaussian H) := hΦ.continuous.measurable.sub measurable_const
    have he := congrArg (Measure.map R) hs
    rw [Measure.map_map R.measurable (by fun_prop),
      Measure.map_map R.measurable hΦm] at he
    change ((ρ : Measure (H × H)).map p).map (fun z => z.1 + z.2) = _
    rw [Measure.map_map (by fun_prop) hm]
    calc
      _ = (ρ : Measure (H × H)).map (fun z => R (z.1 + z.2)) := by simp only [p,map_add]; rfl
      _ = (stdGaussian H).map (fun z => R (Φ z - ∫ g, Φ g ∂stdGaussian H)) := he
      _ = (stdGaussian H).map (M ∘ L) := by simp only [map_sub, hμ, hRΦ]; rfl
      _ = _ := ((Measure.map_map hM hpL.measurable).symm.trans (congrArg (Measure.map M) hpL.map_eq))

#print axioms rectangular_sum
end Green54RectangularImages
