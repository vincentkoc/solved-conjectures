import Green54FiniteLaws
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-! The variational argument for the Gaussian finite-atom coupling in Hua–Song–Tudose. -/

namespace Green54Softmax

open MeasureTheory Filter Set
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
variable [Fintype I] [Nonempty I]

/-! ## Strict affine support inequalities -/

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

/-! ## The maximum of the dual objective -/

omit [BorelSpace E] in
private theorem gap_smul (γ : Measure E) (p : I → ℝ) (X : I → E) (w : Scores I E)
    {t : ℝ} (ht : 0 ≤ t) : supportGap γ p X (t • w) = t * supportGap γ p X w := by
  have he (x : E) : maxScore (t • w).1 (t • w).2 x = t * maxScore w.1 w.2 x := by
    unfold maxScore
    rw [mul_comm t, Finset.sup'_mul₀ ht]
    congr 1
    funext i
    change t * w.1 i + t * (w.2 i) x = _
    ring
  simp only [supportGap, he, integral_const_mul, mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change p i * (t * w.1 i + t * w.2 i (X i)) = _
  ring

omit [BorelSpace E] in
private theorem radial_gap (γ : Measure E) (p : I → ℝ) (X : I → E) (k : I) {δ : ℝ}
    (hδ : ∀ w : Scores I E, w.1 k = 0 → w.2 k = 0 → ‖w‖ = 1 → δ ≤ supportGap γ p X w)
    (w : Scores I E) (ha : w.1 k = 0) (hb : w.2 k = 0) : δ * ‖w‖ ≤ supportGap γ p X w := by
  by_cases hz : w = 0
  · subst w
    simp [supportGap, maxScore]
  open NormedSpace in
    have hh := hδ (normalize w) (by simp [NormedSpace.normalize, ha])
      (by simp [NormedSpace.normalize, hb]) (norm_normalize hz)
    calc
      _ ≤ supportGap γ p X (normalize w) * ‖w‖ := mul_le_mul_of_nonneg_right hh (norm_nonneg _)
      _ = supportGap γ p X (‖w‖ • normalize w) := by rw [gap_smul γ p X _ (norm_nonneg _), mul_comm]
      _ = _ := by rw [norm_smul_normalize]

/-- Logarithm of the total exponential weight of a finite score vector. -/
noncomputable def logSum (s : I → ℝ) := Real.log (∑ i, Real.exp (s i))

private theorem exp_sum_pos (s : I → ℝ) : 0 < ∑ i, Real.exp (s i) :=
  Finset.sum_pos (fun i _ => Real.exp_pos (s i)) Finset.univ_nonempty

private theorem logSum_mono {s t : I → ℝ} (h : ∀ i, s i ≤ t i) : logSum s ≤ logSum t :=
  Real.log_le_log (exp_sum_pos _) (Finset.sum_le_sum fun i _ => Real.exp_le_exp.mpr (h i))

private theorem logSum_shift (s : I → ℝ) (c : ℝ) : logSum (fun i => s i + c) = logSum s + c := by
  simp only [logSum, Real.exp_add, ← Finset.sum_mul, Real.log_mul (exp_sum_pos _).ne' (Real.exp_pos _).ne',
    Real.log_exp]

private theorem logSum_abs_sub {s t : I → ℝ} {L : ℝ} (h : ∀ i, |s i - t i| ≤ L) :
    |logSum s - logSum t| ≤ L := by
  have h₁ := logSum_mono (s := s) (t := fun i => t i + L) fun i => by have := (abs_le.mp (h i)).2; linarith
  have h₂ := logSum_mono (s := t) (t := fun i => s i + L) fun i => by have := (abs_le.mp (h i)).1; linarith
  rw [logSum_shift] at h₁ h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

omit [Nonempty I] in
private theorem score_le_logSum (s : I → ℝ) (i : I) : s i ≤ logSum s := by
  rw [← Real.log_exp (s i)]
  exact Real.log_le_log (Real.exp_pos _) (Finset.single_le_sum (fun j _ => (Real.exp_pos (s j)).le) (Finset.mem_univ i))

/-- Log partition function of the affine scores at a point. -/
noncomputable def logPartition (w : Scores I E) (x : E) := logSum (fun i => w.1 i + w.2 i x)

omit [MeasurableSpace E] [BorelSpace E] in
private theorem continuous_logPartition (w : Scores I E) : Continuous (logPartition w) := by
  apply Continuous.log _ (fun x => (exp_sum_pos (fun i => w.1 i + w.2 i x)).ne')
  exact continuous_finsetSum _ fun i _ => (continuous_const.add (w.2 i).continuous).rexp

omit [MeasurableSpace E] [BorelSpace E] in
private theorem logPartition_diff (w z : Scores I E) (x : E) :
    ‖logPartition w x - logPartition z x‖ ≤ ‖w-z‖ * (1+‖x‖) :=
  logSum_abs_sub (fun i => score_diff_bound x w z i)

private theorem integrable_logPartition (γ : Measure E) [IsProbabilityMeasure γ]
    (hfirst : Integrable (fun x : E => ‖x‖) γ) (w : Scores I E) : Integrable (logPartition w) γ := by
  let c := logSum (fun _ : I => (0 : ℝ))
  have hzero (x : E) : logPartition (0 : Scores I E) x = c := by simp [c, logPartition]
  have hi := (((integrable_const (1:ℝ)).add hfirst).const_mul ‖w‖).add (integrable_const ‖c‖)
  apply hi.mono' (continuous_logPartition w).aestronglyMeasurable
  refine ae_of_all _ fun x => ?_
  have h := logPartition_diff w 0 x
  rw [sub_zero, hzero] at h
  calc
    _ ≤ ‖logPartition w x - c‖ + ‖c‖ := by simpa using norm_add_le (logPartition w x - c) c
    _ ≤ _ := add_le_add_left h _

/-- Dual objective for the entropy maximization problem with the unweighted
log partition. The constant log weights can be absorbed into the intercepts. -/
noncomputable def objective (γ : Measure E) (p : I → ℝ) (X : I → E) (w : Scores I E) : ℝ :=
  (∑ i, p i * (w.1 i + w.2 i (X i))) - ∫ x, logPartition w x ∂γ

private theorem continuous_objective (γ : Measure E) [IsProbabilityMeasure γ]
    (hfirst : Integrable (fun x : E => ‖x‖) γ) (p : I → ℝ) (X : I → E) : Continuous (objective γ p X) := by
  apply Continuous.sub
  · apply continuous_finsetSum
    intro i _
    exact continuous_const.mul (((continuous_apply i).comp continuous_fst).add
      (((ContinuousLinearMap.apply ℝ ℝ (X i)).continuous).comp ((continuous_apply i).comp continuous_snd)))
  let B := ∫ x, (1+‖x‖) ∂γ
  have hB : 0 ≤ B := integral_nonneg fun x => by positivity
  apply ((lipschitzWith_iff_dist_le_mul (K := ⟨B,hB⟩)).mpr ?_).continuous
  intro w z
  rw [dist_eq_norm, dist_eq_norm, ← integral_sub (integrable_logPartition γ hfirst w) (integrable_logPartition γ hfirst z)]
  calc
    _ ≤ ∫ x, ‖logPartition w x - logPartition z x‖ ∂γ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖w-z‖ * (1+‖x‖) ∂γ := integral_mono
      ((integrable_logPartition γ hfirst w).sub (integrable_logPartition γ hfirst z)).norm
      (((integrable_const (1 : ℝ)).add hfirst).const_mul _) (fun x => logPartition_diff w z x)
    _ = _ := by rw [integral_const_mul, mul_comm]; rfl

private theorem objective_le_neg_gap (γ : Measure E) [IsProbabilityMeasure γ]
    (hfirst : Integrable (fun x : E => ‖x‖) γ) (p : I → ℝ) (X : I → E) (w : Scores I E) :
    objective γ p X w ≤ -supportGap γ p X w := by
  have hv (v : E →L[ℝ] ℝ) : Integrable v γ :=
    (hfirst.const_mul ‖v‖).mono' v.continuous.aestronglyMeasurable (ae_of_all _ v.le_opNorm)
  have h := integral_mono (integrable_maxScore γ w.1 w.2 fun _ => hv _)
    (integrable_logPartition γ hfirst w) (fun x => Finset.sup'_le _ _ fun i _ =>
      score_le_logSum (fun j => w.1 j + w.2 j x) i)
  unfold objective supportGap
  linarith

/-- The dual objective attains a maximum after fixing one affine score to zero. -/
theorem exists_anchored_max [FiniteDimensional ℝ E] (γ : Measure E) [IsProbabilityMeasure γ]
    [γ.IsOpenPosMeasure] (p : I → ℝ) (hp : ∀ i, 0 < p i) (X : I → E) {r : ℝ}
    (hr : 0 < r) (hr' : r < 1) (hfirst : Integrable (fun x : E => ‖x‖) γ)
    (hc : ∀ v : E →L[ℝ] ℝ, ∫ x, v x ∂γ = 0)
    (hcx : ∀ f : C(E, ℝ), ConvexOn ℝ univ f → Integrable (fun x => f (r • x)) γ →
      ∑ i, p i * f (X i) ≤ ∫ x, f (r • x) ∂γ)
    (k : I) : ∃ w : Scores I E, w.1 k = 0 ∧ w.2 k = 0 ∧
      ∀ z : Scores I E, z.1 k = 0 → z.2 k = 0 → objective γ p X z ≤ objective γ p X w := by
  classical
  obtain ⟨δ, hδ, hgap⟩ := uniform_unit_gap γ p hp X hr hr' hfirst hc hcx k
  let f := objective γ p X
  let R := max 0 (-(f 0) / δ)
  let T := Metric.closedBall (0 : Scores I E) R ∩ {w : Scores I E | w.1 k = 0 ∧ w.2 k = 0}
  have hT : IsCompact T := (isCompact_closedBall _ _).inter_right
    ((isClosed_eq ((continuous_apply k).comp continuous_fst) continuous_const).inter
      (isClosed_eq ((continuous_apply k).comp continuous_snd) continuous_const))
  have h0 : 0 ∈ T := ⟨Metric.mem_closedBall_self (le_max_left _ _), rfl, rfl⟩
  obtain ⟨w, hw, hm⟩ := hT.exists_isMaxOn ⟨0,h0⟩ (continuous_objective γ hfirst p X).continuousOn
  refine ⟨w, hw.2.1, hw.2.2, fun z hu hv => ?_⟩
  by_cases hz : ‖z‖ ≤ R
  · exact hm ⟨by simpa [Metric.mem_closedBall] using hz, hu, hv⟩
  apply le_trans _ (hm h0)
  have hl := radial_gap γ p X k hgap z hu hv
  have hn : -(f 0) / δ ≤ ‖z‖ := (le_max_right _ _).trans (le_of_not_ge hz)
  have ha := (div_le_iff₀ hδ).mp hn
  have hb := objective_le_neg_gap γ hfirst p X z
  change objective γ p X z ≤ f 0
  linarith only [ha, hl, hb, mul_comm δ ‖z‖]

#print axioms exists_anchored_max

omit [Nonempty I] in
private theorem target_centered (γ : Measure E) [IsProbabilityMeasure γ] (p : I → ℝ) (X : I → E)
    (r : ℝ) (hfirst : Integrable (fun x : E => ‖x‖) γ) (hc : ∀ v : E →L[ℝ] ℝ, ∫ x, v x ∂γ = 0)
    (hcx : ∀ f : C(E, ℝ), ConvexOn ℝ univ f → Integrable (fun x => f (r • x)) γ →
      ∑ i, p i * f (X i) ≤ ∫ x, f (r • x) ∂γ)
    (v : E →L[ℝ] ℝ) : ∑ i, p i * v (X i) = 0 := by
  have hle (b : E →L[ℝ] ℝ) : ∑ i, p i * b (X i) ≤ 0 := by
    have hi : Integrable b γ := (hfirst.const_mul ‖b‖).mono' b.continuous.aestronglyMeasurable (ae_of_all _ b.le_opNorm)
    have hs : Integrable (fun x => b (r • x)) γ := by simpa [map_smul] using hi.const_mul r
    have h := hcx ⟨b, b.continuous⟩ (b.toLinearMap.convexOn convex_univ) hs
    change (∑ i, p i * b (X i)) ≤ ∫ x, b (r • x) ∂γ at h
    simpa only [map_smul, smul_eq_mul, integral_const_mul, hc b, mul_zero] using h
  refine le_antisymm (hle v) ?_
  simpa only [neg_apply, mul_neg, Finset.sum_neg_distrib, neg_nonpos] using hle (-v)

private def anchor (k : I) (w : Scores I E) : Scores I E :=
  (fun i => w.1 i - w.1 k, fun i => w.2 i - w.2 k)

private theorem objective_anchor (γ : Measure E) [IsProbabilityMeasure γ] (p : I → ℝ)
    (hp : ∑ i, p i = 1) (X : I → E) (hcX : ∀ v : E →L[ℝ] ℝ, ∑ i, p i * v (X i) = 0)
    (hfirst : Integrable (fun x : E => ‖x‖) γ) (hc : ∀ v : E →L[ℝ] ℝ, ∫ x, v x ∂γ = 0)
    (k : I) (w : Scores I E) : objective γ p X (anchor k w) = objective γ p X w := by
  have he (x : E) : logPartition (anchor k w) x = logPartition w x - (w.1 k + w.2 k x) := by
    change logSum _ = logSum _ + -(w.1 k + w.2 k x)
    rw [← logSum_shift]
    congr 1
    funext i
    change (w.1 i - w.1 k) + (w.2 i - w.2 k) x = _
    simp only [sub_apply]
    ring
  have hi : Integrable (w.2 k) γ :=
    (hfirst.const_mul ‖w.2 k‖).mono' (w.2 k).continuous.aestronglyMeasurable (ae_of_all _ (w.2 k).le_opNorm)
  have hsum : ∑ i, p i * ((anchor k w).1 i + (anchor k w).2 i (X i)) =
      (∑ i, p i * (w.1 i + w.2 i (X i))) - w.1 k := by
    calc
      _ = ∑ i, (p i * (w.1 i + w.2 i (X i)) - p i * w.1 k - p i * w.2 k (X i)) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [anchor, sub_apply]
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hp, one_mul, hcX, sub_zero]
  have hb : Integrable (fun x : E => w.1 k + w.2 k x) γ := (integrable_const _).add hi
  have hmean : (∫ x, w.1 k + w.2 k x ∂γ) = w.1 k := by
    rw [integral_add (integrable_const (w.1 k)) hi, integral_const, probReal_univ, one_smul, hc, add_zero]
  simp only [objective, he, hsum, integral_sub (integrable_logPartition γ hfirst w) hb, hmean]
  ring

/-- The dual objective attains a global maximum under strict convex domination. -/
theorem exists_maximum [FiniteDimensional ℝ E] (γ : Measure E) [IsProbabilityMeasure γ]
    [γ.IsOpenPosMeasure] (p : I → ℝ) (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1) (X : I → E) {r : ℝ}
    (hr : 0 < r) (hr' : r < 1) (hfirst : Integrable (fun x : E => ‖x‖) γ)
    (hc : ∀ v : E →L[ℝ] ℝ, ∫ x, v x ∂γ = 0)
    (hcx : ∀ f : C(E, ℝ), ConvexOn ℝ univ f → Integrable (fun x => f (r • x)) γ →
      ∑ i, p i * f (X i) ≤ ∫ x, f (r • x) ∂γ) :
    ∃ w : Scores I E, ∀ z, objective γ p X z ≤ objective γ p X w := by
  let k : I := Classical.choice inferInstance
  obtain ⟨w, _, _, hw⟩ := exists_anchored_max γ p hp X hr hr' hfirst hc hcx k
  refine ⟨w, fun z => ?_⟩
  rw [← objective_anchor γ p hp1 X (target_centered γ p X r hfirst hc hcx) hfirst hc k z]
  exact hw _ (sub_self _) (sub_self _)

#print axioms exists_maximum

/-! ## Conditional masses and moments -/

def affineScore (w : Scores I E) (i : I) (x : E) := w.1 i + w.2 i x

/-- Probability assigned to a row by the softmax at x. -/
noncomputable def weight (w : Scores I E) (i : I) (x : E) : ℝ :=
  Real.exp (affineScore w i x) / ∑ j, Real.exp (affineScore w j x)

omit [MeasurableSpace E] [BorelSpace E] in
private theorem weight_pos (w : Scores I E) (i : I) (x : E) : 0 < weight w i x :=
  div_pos (Real.exp_pos _) (exp_sum_pos _)

omit [MeasurableSpace E] [BorelSpace E] in
private theorem sum_weight (w : Scores I E) (x : E) : ∑ i, weight w i x = 1 := by
  simp only [weight, ← Finset.sum_div, div_self (exp_sum_pos _).ne']

omit [MeasurableSpace E] [BorelSpace E] in
private theorem continuous_weight (w : Scores I E) (i : I) : Continuous (weight w i) := by
  have h (j : I) : Continuous fun x => Real.exp (affineScore w j x) :=
    (continuous_const.add (w.2 j).continuous).rexp
  exact (h i).div (continuous_finsetSum _ fun j _ => h j) (fun x => (exp_sum_pos _).ne')

omit [MeasurableSpace E] [BorelSpace E] [Nonempty I] [Fintype I] in
private theorem affineScore_line (w d : Scores I E) (t : ℝ) (i : I) (x : E) :
    affineScore (w + t • d) i x = affineScore w i x + t * affineScore d i x := by
  change (w.1 i + t * d.1 i) + (w.2 i x + t * d.2 i x) = _
  unfold affineScore
  ring

omit [MeasurableSpace E] [BorelSpace E] in
private theorem hasDerivAt_logPartition (w d : Scores I E) (t : ℝ) (x : E) :
    HasDerivAt (fun t => logPartition (w + t • d) x)
      (∑ i, weight (w + t • d) i x * affineScore d i x) t := by
  have h (i) : HasDerivAt (fun t => affineScore (w+t•d) i x) (affineScore d i x) t := by
    simp_rw [affineScore_line]
    simpa using ((hasDerivAt_id t).mul_const (affineScore d i x)).const_add (affineScore w i x)
  have hh := (HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (h i).exp).log
    (exp_sum_pos (fun i => affineScore (w+t•d) i x)).ne'
  apply hh.congr_deriv
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  unfold weight
  ring

omit [MeasurableSpace E] [BorelSpace E] in
private theorem deriv_bound (w d : Scores I E) (x : E) :
    ‖∑ i, weight w i x * affineScore d i x‖ ≤ ‖d‖ * (1+‖x‖) := by
  calc
    _ ≤ ∑ i, ‖weight w i x * affineScore d i x‖ := norm_sum_le _ _
    _ ≤ ∑ i, weight w i x * (‖d‖ * (1+‖x‖)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (weight_pos w i x)]
      apply mul_le_mul_of_nonneg_left _ (weight_pos w i x).le
      simpa [affineScore] using score_diff_bound x d 0 i
    _ = _ := by rw [← Finset.sum_mul, sum_weight, one_mul]

private theorem integral_direction (γ : Measure E) [IsProbabilityMeasure γ]
    (hfirst : Integrable (fun x : E => ‖x‖) γ) (w d : Scores I E) :
    HasDerivAt (fun t : ℝ => ∫ x, logPartition (w+t•d) x ∂γ)
      (∫ x, ∑ i, weight w i x * affineScore d i x ∂γ) 0 := by
  let D (t : ℝ) (x : E) := ∑ i, weight (w+t•d) i x * affineScore d i x
  have hD (t) : Continuous (D t) := continuous_finsetSum _ fun i _ =>
    (continuous_weight _ _).mul (continuous_const.add (d.2 i).continuous)
  have hmeas (t : ℝ) : AEStronglyMeasurable (logPartition (w+t•d)) γ :=
    (continuous_logPartition (w+t•d)).aestronglyMeasurable
  have ht := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := γ) (s := univ)
    (x₀ := (0:ℝ)) (F := fun t x => logPartition (w + t • d) x) (F' := D)
    (bound := fun x => ‖d‖ * (1+‖x‖)) univ_mem
    (Eventually.of_forall hmeas)
    (integrable_logPartition γ hfirst (w+(0:ℝ)•d)) (hD 0).aestronglyMeasurable
    (ae_of_all _ fun x t _ => deriv_bound (w+t•d) d x)
    (((integrable_const (1:ℝ)).add hfirst).const_mul ‖d‖)
    (ae_of_all _ fun x t _ => hasDerivAt_logPartition w d t x)
  simpa only [D, zero_smul, add_zero] using ht.2

private theorem stationarity (γ : Measure E) [IsProbabilityMeasure γ]
    (hfirst : Integrable (fun x : E => ‖x‖) γ) (p : I → ℝ) (X : I → E) (w : Scores I E)
    (hw : ∀ z, objective γ p X z ≤ objective γ p X w) (d : Scores I E) :
    ∑ i, p i * affineScore d i (X i) = ∫ x, ∑ i, weight w i x * affineScore d i x ∂γ := by
  have h (i) : HasDerivAt (fun t : ℝ => p i * affineScore (w+t•d) i (X i))
      (p i * affineScore d i (X i)) 0 := by
    apply HasDerivAt.const_mul
    simp_rw [affineScore_line]
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (affineScore d i (X i))).const_add (affineScore w i (X i))
  have hm : IsLocalMax (fun t : ℝ => objective γ p X (w+t•d)) 0 :=
    Eventually.of_forall fun t => by simpa only [zero_smul, add_zero] using hw (w+t•d)
  exact sub_eq_zero.mp (hm.hasDerivAt_eq_zero
    ((HasDerivAt.fun_sum (u := Finset.univ) fun i _ => h i).sub (integral_direction γ hfirst w d)))

private theorem row_moment (γ : Measure E) [IsProbabilityMeasure γ]
    (hfirst : Integrable (fun x : E => ‖x‖) γ) (p : I → ℝ) (X : I → E) (w : Scores I E)
    (hw : ∀ z, objective γ p X z ≤ objective γ p X w) (i : I) (a : ℝ) (v : E →L[ℝ] ℝ) :
    p i * (a + v (X i)) = ∫ x, weight w i x * (a + v x) ∂γ := by
  classical
  let d : Scores I E := (Pi.single i a, Pi.single i v)
  have he (x : E) : affineScore d i x = a + v x := by simp [affineScore, d]
  have hz (j : I) (hj : j ≠ i) (x : E) : affineScore d j x = 0 := by
    simp [affineScore, d, Pi.single_eq_of_ne hj]
  have hpre := stationarity γ hfirst p X w hw d
  have hleft : ∑ j, p j * affineScore d j (X j) = p i * (a + v (X i)) := by
    rw [Finset.sum_eq_single i, he]
    · intro j _ hj
      simp [hz j hj]
    · simp
  have hright (x : E) : ∑ j, weight w j x * affineScore d j x = weight w i x * (a + v x) := by
    rw [Finset.sum_eq_single i, he]
    · intro j _ hj
      simp [hz j hj]
    · simp
  simpa only [hleft, hright] using hpre

omit [MeasurableSpace E] [BorelSpace E] [Fintype I] [Nonempty I] in
private theorem affineScore_combine (w : Scores I E) (i : I) (x y : E) {a b : ℝ} (hab : a+b=1) :
    affineScore w i (a • x + b • y) = a * affineScore w i x + b * affineScore w i y := by
  simp only [affineScore, map_add, map_smul, smul_eq_mul]
  linear_combination -(w.1 i) * hab

omit [MeasurableSpace E] [BorelSpace E] in
private theorem convex_logPartition (w : Scores I E) : ConvexOn ℝ univ (logPartition w) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x + b • y
  let C := a * logPartition w x + b * logPartition w y
  have hweight (j : I) (x : E) : Real.exp (affineScore w j x - logPartition w x) = weight w j x := by
    rw [Real.exp_sub, show Real.exp (logPartition w x) = _ from Real.exp_log (exp_sum_pos _)]
    rfl
  have h (j : I) : Real.exp (affineScore w j z - C) ≤ a * weight w j x + b * weight w j y := by
    have he : affineScore w j z - C = a*(affineScore w j x-logPartition w x) + b*(affineScore w j y-logPartition w y) := by
      dsimp only [z,C]
      rw [affineScore_combine w j x y hab]
      ring
    rw [he, ← hweight, ← hweight]
    exact convexOn_exp.2 (mem_univ _) (mem_univ _) ha hb hab
  have hs := Finset.sum_le_sum (s := Finset.univ) fun j _ => h j
  simp only [Real.exp_sub, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, sum_weight, mul_one, hab] at hs
  have hle := (div_le_one (Real.exp_pos C)).mp hs
  change Real.log (∑ i, Real.exp (affineScore w i z)) ≤ C
  simpa only [Real.log_exp] using Real.log_le_log (exp_sum_pos _) hle

omit [MeasurableSpace E] [BorelSpace E] in
private theorem concave_log_weight (w : Scores I E) (i : I) : ConcaveOn ℝ univ (fun x => Real.log (weight w i x)) := by
  have he (x : E) : Real.log (weight w i x) = affineScore w i x - logPartition w x := by
    rw [weight, Real.log_div (Real.exp_pos _).ne' (exp_sum_pos _).ne', Real.log_exp]
    rfl
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h := (convex_logPartition w).2 (mem_univ x) (mem_univ y) ha hb hab
  simp only [smul_eq_mul] at h
  simp only [he, smul_eq_mul, affineScore_combine w i x y hab]
  linarith

/-- Conditional density of the reference vector for an atom of mass pᵢ. -/
noncomputable def density (p : I → ℝ) (w : Scores I E) (i : I) (x : E) : ℝ := weight w i x / p i

/-- The softmax components form a pointwise partition of the reference law, have unit mass,
and have the atom locations as their conditional means in every linear direction. -/
def HasConditionalDensities (γ : Measure E) (p : I → ℝ) (X : I → E) (w : Scores I E) : Prop :=
  (∀ x, ∑ i, p i * density p w i x = 1) ∧ ∀ i,
    (∀ x, 0 < density p w i x) ∧ Continuous (density p w i) ∧
    ConcaveOn ℝ univ (fun x => Real.log (density p w i x)) ∧
    (∫ x, density p w i x ∂γ) = 1 ∧
    ∀ v : E →L[ℝ] ℝ, (∫ x, density p w i x * v x ∂γ) = v (X i)

/-- Existence direction of the softmax representation for a finite atomic law below
a strict contraction of a centered, full-support reference law with finite first moment. -/
theorem exists_softmax_densities [FiniteDimensional ℝ E] (γ : Measure E) [IsProbabilityMeasure γ]
    [γ.IsOpenPosMeasure] (p : I → ℝ) (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1) (X : I → E) {r : ℝ}
    (hr : 0 < r) (hr' : r < 1) (hfirst : Integrable (fun x : E => ‖x‖) γ)
    (hc : ∀ v : E →L[ℝ] ℝ, ∫ x, v x ∂γ = 0)
    (hcx : ∀ f : C(E, ℝ), ConvexOn ℝ univ f → Integrable (fun x => f (r • x)) γ →
      ∑ i, p i * f (X i) ≤ ∫ x, f (r • x) ∂γ) : ∃ w, HasConditionalDensities γ p X w := by
  obtain ⟨w, hw⟩ := exists_maximum γ p hp hp1 X hr hr' hfirst hc hcx
  refine ⟨w, fun x => ?_, fun i => ⟨fun x => div_pos (weight_pos w i x) (hp i),
    (continuous_weight w i).div_const _, ?_, ?_, fun v => ?_⟩⟩
  · simpa only [density, mul_div_cancel₀ _ (hp _).ne'] using sum_weight w x
  · have h : (fun x => Real.log (density p w i x)) = (fun x => Real.log (weight w i x) - Real.log (p i)) :=
      funext fun x => Real.log_div (weight_pos w i x).ne' (hp i).ne'
    rw [h]
    exact (concave_log_weight w i).sub (convexOn_const _ convex_univ)
  · have h := row_moment γ hfirst p X w hw i 1 0
    simp only [zero_apply, add_zero, mul_one] at h
    rw [show (∫ x, density p w i x ∂γ) = (∫ x, weight w i x ∂γ) / p i from integral_div _ _, ← h, div_self (hp i).ne']
  · have h := row_moment γ hfirst p X w hw i 0 v
    simp only [zero_add] at h
    calc
      _ = ∫ x, (weight w i x * v x) / p i ∂γ := integral_congr_ae (ae_of_all _ fun x => by unfold density; ring)
      _ = _ := by rw [integral_div, ← h, mul_div_cancel_left₀ _ (hp i).ne']

#print axioms exists_softmax_densities

open Green54ConvexTests ProbabilityTheory

private theorem gaussian_integrable_id (J : Finset ℕ) :
    Integrable (fun x : J → ℝ => x) (finiteGaussian J) := by
  apply integrable_pi_iff.mpr
  intro j
  exact integrable_eval (μ := fun _ : J => gaussianReal 0 1) IsGaussian.integrable_id

private theorem gaussian_centered (J : Finset ℕ) (v : (J → ℝ) →L[ℝ] ℝ) :
    (∫ x, v x ∂finiteGaussian J) = 0 := by
  have hi := gaussian_integrable_id J
  have hz : (∫ x, x ∂finiteGaussian J) = 0 := by
    ext j
    change (ContinuousLinearMap.proj j : (J → ℝ) →L[ℝ] ℝ) (∫ x, x ∂finiteGaussian J) = 0
    rw [← ContinuousLinearMap.integral_comp_comm _ hi]
    exact (integral_eval (μ := fun _ : J => gaussianReal 0 1)).trans integral_id_gaussianReal
  rw [v.integral_comp_comm hi, hz, map_zero]

/-- For every finite target in the Green 54 reduction, the positive atoms admit
log-concave conditional Gaussian densities with the exact prescribed means. -/
theorem gaussian_finite_conditionals (J : Finset ℕ) {F : Set (J → ℝ)} (hF : F.Finite)
    (ν : ProbabilityMeasure F) {r : ℝ} (hr : 0 < r) (hr' : r < 1)
    (hdom : ConvexDominated ((ν : Measure F).map Subtype.val) ((finiteGaussian J).map (fun x => r • x))) :
    ∃ (s : Finset F) (w : Scores s (J → ℝ)),
      (∀ i : s, 0 < (ν : Measure F).real {i.val}) ∧
      (∑ i : s, (ν : Measure F).real {i.val}) = 1 ∧
      ((ν : Measure F).map Subtype.val = ∑ i : s, ENNReal.ofReal ((ν : Measure F).real {i.val}) •
        Measure.dirac i.val.val) ∧
      HasConditionalDensities (finiteGaussian J) (fun i : s => (ν : Measure F).real {i.val})
        (fun i => i.val.val) w := by
  classical
  let : Fintype F := hF.fintype
  let m (x : F) := (ν : Measure F).real {x}
  let s := Finset.univ.filter (fun x : F => 0 < m x)
  have hpos (x : s) : 0 < m x.val := (Finset.mem_filter.mp x.property).2
  have hz (x : F) (hx : x ∉ s) : m x = 0 := by
    have := not_lt.mp fun hp => hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
    exact le_antisymm this measureReal_nonneg
  have hint (g : F → ℝ) : ∑ i : s, m i.val * g i.val = ∫ x, g x ∂(ν : Measure F) := by
    rw [integral_fintype Integrable.of_finite, Finset.sum_coe_sort s (fun x => m x * g x)]
    simp only [smul_eq_mul]
    exact Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by rw [hz x hx, zero_mul])
  have hp1 : ∑ i : s, m i.val = 1 := by simpa using hint (fun _ => 1)
  let : Nonempty s := by
    by_contra hn
    have : IsEmpty s := not_nonempty_iff.mp hn
    simp at hp1
  let : (gaussianReal 0 1).IsOpenPosMeasure := (gaussianReal_absolutelyContinuous' 0 one_ne_zero).isOpenPosMeasure
  have hd : ∀ f : C(J → ℝ, ℝ), ConvexOn ℝ univ f → Integrable (fun x => f (r • x)) (finiteGaussian J) →
      ∑ i : s, m i.val * f i.val.val ≤ ∫ x, f (r • x) ∂finiteGaussian J := by
    intro f hf hi
    have hm : Measurable (fun x : J → ℝ => r • x) := by fun_prop
    have hi' := (integrable_map_measure f.continuous.aestronglyMeasurable hm.aemeasurable).mpr hi
    have hh := hdom f hf hi'
    rw [integral_map measurable_subtype_coe.aemeasurable f.continuous.aestronglyMeasurable,
      integral_map hm.aemeasurable f.continuous.aestronglyMeasurable] at hh
    exact (hint (fun x => f x.val)).trans_le hh
  obtain ⟨w, hw⟩ := exists_softmax_densities (finiteGaussian J) _ hpos hp1 _ hr hr'
    (gaussian_integrable_id J).norm (gaussian_centered J) hd
  refine ⟨s, w, hpos, hp1, ?_, hw⟩
  have hfull := Measure.sum_smul_dirac (ν : Measure F)
  rw [Measure.sum_fintype] at hfull
  calc
    _ = ∑ a : F, (ν : Measure F) {a} • Measure.dirac a.val := by
      conv_lhs => rw [← hfull]
      rw [Measure.map_finset_sum measurable_subtype_coe.aemeasurable]
      simp only [Measure.map_smul, Measure.map_dirac]
    _ = ∑ a : F, ENNReal.ofReal (m a) • Measure.dirac a.val := by
      simp only [m, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ = _ := by
      rw [Finset.sum_coe_sort s (fun a : F => ENNReal.ofReal (m a) • Measure.dirac a.val)]
      exact (Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by simp [hz x hx])).symm

#print axioms gaussian_finite_conditionals

end Green54Softmax
