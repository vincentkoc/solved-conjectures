import Green54FiniteLaws

/-! The variational argument for the Gaussian finite-atom coupling in Hua–Song–Tudose. -/

namespace Green54Softmax
open MeasureTheory Filter Set
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
variable [Fintype I] [Nonempty I]
omit [MeasurableSpace E] [BorelSpace E] in
private theorem affine_cross {v w : E →L[ℝ] ℝ} (hne : v ≠ w) (a b : ℝ) :
    ∃ x, a + v x < b + w x := by
  obtain ⟨x, hx⟩ : ∃ x, v x ≠ w x := by
    by_contra! he
    exact hne (ContinuousLinearMap.ext he)
  let t := (b-a-1) / (v x - w x)
  have he : t * (v x-w x) = b-a-1 := div_mul_cancel₀ _ (sub_ne_zero.mpr hx)
  refine ⟨t • x, ?_⟩
  simp only [map_smul, smul_eq_mul]
  linarith only [he]
omit [BorelSpace E] in
private theorem max_affine_strict (μ : Measure E) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (u : I → ℝ) (v : I → E →L[ℝ] ℝ) (f : E → ℝ) (hf : Continuous f) (hi : Integrable f μ)
    (hlo : ∀ i x, u i + v i x ≤ f x) (hzero : f 0 = Finset.univ.sup' Finset.univ_nonempty u)
    (hv : ∀ i, Integrable (v i) μ) (hc : ∀ i, ∫ x, v i x ∂μ = 0)
    (hne : ∃ i j, v i ≠ v j) : f 0 < ∫ x, f x ∂μ := by
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty u
  obtain ⟨j, hj⟩ : ∃ j, v k ≠ v j := by
    by_contra! ha
    obtain ⟨i,j,h⟩ := hne
    exact h ((ha i).symm.trans (ha j))
  obtain ⟨x, hx⟩ := affine_cross hj (u k) (u j)
  let g (y : E) := u k + v k y
  have hgi : Integrable g μ := (integrable_const _).add (hv k)
  have hmean : ∫ y, g y ∂μ = f 0 := by simp [g,integral_add (integrable_const _) (hv k),hc k,hzero,hk]
  rw [← hmean]
  apply lt_of_le_of_ne (integral_mono hgi hi (hlo k))
  intro he
  have hgf := (integral_eq_iff_of_ae_le hgi hi (ae_of_all _ (hlo k))).mp he
  have heq : g = f := MeasureTheory.Measure.eq_of_ae_eq hgf (continuous_const.add (v k).continuous) hf
  exact (hx.trans_le (hlo j x)).ne (congrFun heq x)
/-- Upper envelope of a nonempty finite family of affine functions. -/
noncomputable def maxScore (u : I → ℝ) (v : I → E →L[ℝ] ℝ) (x : E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => u i + v i x
omit [MeasurableSpace E] [BorelSpace E] in
private theorem le_maxScore (u : I → ℝ) (v : I → E →L[ℝ] ℝ) (i : I) (x : E) :
    u i + v i x ≤ maxScore u v x := Finset.le_sup' (fun j => u j + v j x) (Finset.mem_univ i)
omit [MeasurableSpace E] [BorelSpace E] in
private theorem continuous_maxScore (u : I → ℝ) (v : I → E →L[ℝ] ℝ) : Continuous (maxScore u v) :=
  Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ => continuous_const.add (v i).continuous)
omit [MeasurableSpace E] [BorelSpace E] in
private theorem convex_maxScore (u : I → ℝ) (v : I → E →L[ℝ] ℝ) : ConvexOn ℝ univ (maxScore u v) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  apply Finset.sup'_le
  intro i _
  calc
    u i + v i (a • x + b • y) = a * (u i + v i x) + b * (u i + v i y) := by
      simp only [map_add, map_smul, smul_eq_mul]
      linear_combination -(u i) * hab
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (le_maxScore u v i x) ha)
      (mul_le_mul_of_nonneg_left (le_maxScore u v i y) hb)
private theorem integrable_maxScore (μ : Measure E) [IsProbabilityMeasure μ] (u : I → ℝ)
    (v : I → E →L[ℝ] ℝ) (hv : ∀ i, Integrable (v i) μ) : Integrable (maxScore u v) μ := by
  have hi : Integrable (fun x => ∑ i, ‖u i + v i x‖) μ :=
    integrable_finsetSum _ fun i _ => ((integrable_const (u i)).add (hv i)).norm
  apply hi.mono' (continuous_maxScore u v).aestronglyMeasurable
  apply ae_of_all
  intro x
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => u i + v i x)
  change ‖Finset.univ.sup' _ _‖ ≤ _
  rw [hk]
  exact Finset.single_le_sum (fun i _ => norm_nonneg (u i + v i x)) (Finset.mem_univ k)
/-- A finite target below a strict contraction of a centered, full-support law lies
strictly inside each nonconstant finite affine support inequality. -/
theorem strict_support_gap (γ : Measure E) [IsProbabilityMeasure γ] [γ.IsOpenPosMeasure]
    (p : I → ℝ) (hp : ∀ i, 0 < p i) (X : I → E) {r : ℝ} (hr : 0 < r) (hr' : r < 1)
    (hcx : ∀ f : C(E, ℝ), ConvexOn ℝ univ f → Integrable (fun x => f (r • x)) γ →
      ∑ i, p i * f (X i) ≤ ∫ x, f (r • x) ∂γ)
    (u : I → ℝ) (v : I → E →L[ℝ] ℝ) (hv : ∀ i, Integrable (v i) γ)
    (hc : ∀ i, ∫ x, v i x ∂γ = 0) (hne : (∃ i j, v i ≠ v j) ∨ ∃ i j, u i < u j) :
    ∑ i, p i * (u i + v i (X i)) < ∫ x, maxScore u v x ∂γ := by
  classical
  let M := maxScore u v
  have hi : Integrable M γ := integrable_maxScore γ u v hv
  have his : Integrable (fun x => M (r • x)) γ := by
    have he : (fun x => M (r • x)) = maxScore u (fun i => r • v i) := by
      funext x
      simp only [M, maxScore, map_smul, smul_apply]
    rw [he]
    exact integrable_maxScore γ u (fun i => r • v i) (fun i => (hv i).const_mul r)
  have ht := hcx ⟨M, continuous_maxScore u v⟩ (convex_maxScore u v) his
  change ∑ i, p i * M (X i) ≤ ∫ x, M (r • x) ∂γ at ht
  have hzero : M 0 = Finset.univ.sup' Finset.univ_nonempty u := by simp [M, maxScore]
  have hm : M 0 ≤ ∫ x, M x ∂γ := by
    obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty u
    have h := integral_mono ((integrable_const (u k)).add (hv k)) hi (le_maxScore u v k)
    simpa only [Pi.add_apply, integral_add (integrable_const _) (hv k), integral_const, probReal_univ,
      one_smul, hc k, add_zero, hzero, hk] using h
  have hcontract : (∫ x, M (r • x) ∂γ) ≤ r * (∫ x, M x ∂γ) + (1-r) * M 0 := by
    have h : ∀ x, M (r • x) ≤ r * M x + (1-r) * M 0 := fun x => by
      have h := (convex_maxScore u v).2 (x := x) (y := 0) (mem_univ _) (mem_univ _)
        hr.le (sub_nonneg.mpr hr'.le) (by ring : r + (1-r) = 1)
      simpa only [smul_zero, add_zero, smul_eq_mul] using h
    have hi' := (hi.const_mul r).add (integrable_const ((1-r) * M 0))
    have he := integral_mono his hi' h
    change (∫ x, M (r • x) ∂γ) ≤ ∫ x, r * M x + (1-r) * M 0 ∂γ at he
    calc
      _ ≤ ∫ x, r * M x + (1-r) * M 0 ∂γ := he
      _ = (∫ x, r * M x ∂γ) + ∫ _, (1-r) * M 0 ∂γ :=
        integral_add (hi.const_mul r) (integrable_const _)
      _ = _ := by simp [integral_const_mul]
  have hle (i) : p i * (u i + v i (X i)) ≤ p i * M (X i) :=
    mul_le_mul_of_nonneg_left (le_maxScore u v i (X i)) (hp i).le
  by_cases hd : ∃ i j, v i ≠ v j
  · have hs := max_affine_strict γ u v M (continuous_maxScore u v) hi (le_maxScore u v) hzero hv hc hd
    refine (Finset.sum_le_sum fun i _ => hle i).trans_lt (ht.trans_lt (hcontract.trans_lt ?_))
    nlinarith only [mul_pos (sub_pos.mpr hr') (sub_pos.mpr hs)]
  · obtain ⟨i, j, hij⟩ := hne.resolve_left hd
    push Not at hd
    have hs : u i + v i (X i) < M (X i) := by
      calc
        _ < u j + v j (X i) := by rw [hd i j]; linarith
        _ ≤ _ := le_maxScore u v j (X i)
    have hlt := Finset.sum_lt_sum (s := Finset.univ) (fun k _ => hle k)
      ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hs (hp i)⟩
    refine hlt.trans_le (ht.trans (hcontract.trans ?_))
    nlinarith only [mul_nonneg (sub_nonneg.mpr hr'.le) (sub_nonneg.mpr hm)]

#print axioms strict_support_gap

abbrev Scores (I E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (I → ℝ) × (I → E →L[ℝ] ℝ)

omit [MeasurableSpace E] [BorelSpace E] [Nonempty I] in
private theorem score_diff_bound (x : E) (w z : Scores I E) (i : I) :
    ‖(w.1 i + w.2 i x) - (z.1 i + z.2 i x)‖ ≤ ‖w-z‖ * (1+‖x‖) := by
  have ha : ‖w.1 i - z.1 i‖ ≤ ‖w-z‖ := (norm_le_pi_norm (w.1-z.1) i).trans (norm_fst_le (w-z))
  have hb : ‖w.2 i - z.2 i‖ ≤ ‖w-z‖ := (norm_le_pi_norm (w.2-z.2) i).trans (norm_snd_le (w-z))
  have hl := (w.2 i-z.2 i).le_opNorm x
  calc
    _ = ‖(w.1 i - z.1 i) + (w.2 i - z.2 i) x‖ := by congr 1; simp only [sub_apply]; ring
    _ ≤ ‖w.1 i-z.1 i‖ + ‖(w.2 i-z.2 i) x‖ := norm_add_le _ _
    _ ≤ ‖w-z‖ + ‖w-z‖ * ‖x‖ := add_le_add ha (hl.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _)))
    _ = _ := by ring

omit [MeasurableSpace E] [BorelSpace E] in
private theorem max_diff_bound (x : E) (w z : Scores I E) :
    ‖maxScore w.1 w.2 x - maxScore z.1 z.2 x‖ ≤ ‖w-z‖ * (1+‖x‖) := by
  have h (a b : Scores I E) : maxScore a.1 a.2 x ≤ maxScore b.1 b.2 x + ‖a-b‖ * (1+‖x‖) := by
    apply Finset.sup'_le
    intro i _
    have hd := (le_abs_self _).trans (score_diff_bound x a b i)
    linarith only [hd, le_maxScore b.1 b.2 i x]
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have hh := h z w
    rw [norm_sub_rev z w] at hh
    linarith
  · linarith only [h w z]

private theorem continuous_mean_maxScore (γ : Measure E) [IsProbabilityMeasure γ]
    (hfirst : Integrable (fun x : E => ‖x‖) γ) :
    Continuous fun w : Scores I E => ∫ x, maxScore w.1 w.2 x ∂γ := by
  have hv (v : E →L[ℝ] ℝ) : Integrable v γ :=
    (hfirst.const_mul ‖v‖).mono' v.continuous.aestronglyMeasurable (ae_of_all _ v.le_opNorm)
  let B := ∫ x, (1+‖x‖) ∂γ
  have hB : 0 ≤ B := integral_nonneg fun x => by positivity
  apply ((lipschitzWith_iff_dist_le_mul (K := ⟨B,hB⟩)).mpr ?_).continuous
  intro w z
  rw [dist_eq_norm, dist_eq_norm, ← integral_sub (integrable_maxScore γ w.1 w.2 (fun i => hv _))
    (integrable_maxScore γ z.1 z.2 (fun i => hv _))]
  have h₁ := (integrable_maxScore γ w.1 w.2 (fun i => hv _)).sub (integrable_maxScore γ z.1 z.2 (fun i => hv _))
  have h₂ := ((integrable_const (1:ℝ)).add hfirst).const_mul ‖w-z‖
  calc
    _ ≤ ∫ x, ‖maxScore w.1 w.2 x - maxScore z.1 z.2 x‖ ∂γ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖w-z‖ * (1+‖x‖) ∂γ := integral_mono h₁.norm h₂ (fun x => max_diff_bound x w z)
    _ = _ := by rw [integral_const_mul, mul_comm]; rfl



/-- Difference between the expected maximum of the affine scores and the score
assigned to the finite target. -/
noncomputable def supportGap (γ : Measure E) (p : I → ℝ) (X : I → E) (w : Scores I E) : ℝ :=
  (∫ x, maxScore w.1 w.2 x ∂γ) - ∑ i, p i * (w.1 i + w.2 i (X i))

/-- After fixing one row to zero, the affine support gap has a positive minimum
over every nonempty sphere of unit coefficient vectors. -/
theorem uniform_unit_gap [FiniteDimensional ℝ E] (γ : Measure E) [IsProbabilityMeasure γ]
    [γ.IsOpenPosMeasure] (p : I → ℝ) (hp : ∀ i, 0 < p i) (X : I → E) {r : ℝ}
    (hr : 0 < r) (hr' : r < 1) (hfirst : Integrable (fun x : E => ‖x‖) γ)
    (hc : ∀ v : E →L[ℝ] ℝ, ∫ x, v x ∂γ = 0)
    (hcx : ∀ f : C(E, ℝ), ConvexOn ℝ univ f → Integrable (fun x => f (r • x)) γ →
      ∑ i, p i * f (X i) ≤ ∫ x, f (r • x) ∂γ)
    (k : I) : ∃ δ : ℝ, 0 < δ ∧ ∀ w : Scores I E, w.1 k = 0 → w.2 k = 0 →
      ‖w‖ = 1 → δ ≤ supportGap γ p X w := by
  classical
  let T := Metric.sphere (0 : Scores I E) 1 ∩ {w : Scores I E | w.1 k = 0 ∧ w.2 k = 0}
  have hT : IsCompact T := (isCompact_sphere _ _).inter_right
    ((isClosed_eq ((continuous_apply k).comp continuous_fst) continuous_const).inter
      (isClosed_eq ((continuous_apply k).comp continuous_snd) continuous_const))
  have hg : Continuous (supportGap γ p X) := by
    apply (continuous_mean_maxScore γ hfirst).sub
    apply continuous_finsetSum
    intro i _
    apply continuous_const.mul
    apply ((continuous_apply i).comp continuous_fst).add
    exact ((ContinuousLinearMap.apply ℝ ℝ (X i)).continuous).comp ((continuous_apply i).comp continuous_snd)
  have hpos (w : Scores I E) (hw : w ∈ T) : 0 < supportGap γ p X w := by
    apply sub_pos.mpr
    apply strict_support_gap γ p hp X hr hr' hcx w.1 w.2
      (fun i => (hfirst.const_mul ‖w.2 i‖).mono' (w.2 i).continuous.aestronglyMeasurable
        (ae_of_all _ (w.2 i).le_opNorm)) (fun i => hc (w.2 i))
    by_contra! h
    have hv : w.2 = 0 := funext fun i => (h.1 i k).trans hw.2.2
    have hu : w.1 = 0 := funext fun i => (le_antisymm (h.2 k i) (h.2 i k)).trans hw.2.1
    have hw0 : w = 0 := Prod.ext hu hv
    have hm := hw.1
    simp [hw0] at hm
  have hn (w : Scores I E) (hu : w.1 k = 0) (hv : w.2 k = 0) (hn : ‖w‖ = 1) : w ∈ T :=
    ⟨by simpa [Metric.mem_sphere] using hn, hu, hv⟩
  by_cases hne : T.Nonempty
  · obtain ⟨w, hw, hmin⟩ := hT.exists_isMinOn hne hg.continuousOn
    exact ⟨_, hpos w hw, fun z hu hv hz => hmin (hn z hu hv hz)⟩
  · exact ⟨1, zero_lt_one, fun z hu hv hz => (hne ⟨z, hn z hu hv hz⟩).elim⟩

#print axioms uniform_unit_gap

end Green54Softmax
