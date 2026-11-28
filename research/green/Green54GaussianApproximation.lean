import Green54GaussianResampling
import Green54GaussianLinearization

/-! Finite adapted approximations for Lipschitz images of a standard Gaussian.
The average derivative at each step uses only the increments already revealed. -/

noncomputable section
open scoped NNReal
open MeasureTheory ProbabilityTheory Green54Contractions Green54GaussianResampling
namespace Green54GaussianApproximation
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

private def mixedSum {n : ℕ} (k : ℕ) (x w : Fin (n + 1) → E) : E :=
  (Real.sqrt n)⁻¹ • ∑ j, if j.val < k then x j else w j

private def base {n : ℕ} (i : Fin (n + 1)) (x w : Fin (n + 1) → E) : E :=
  normalizedSum n (fun k => if i.succAbove k < i then x (i.succAbove k) else w (i.succAbove k))

omit [Fintype ι] in
private theorem before {n : ℕ} (i : Fin (n + 1)) (x w : Fin (n + 1) → E) :
    mixedSum i.val x w = base i x w + (Real.sqrt n)⁻¹ • w i := by
  simp only [mixedSum, base, normalizedSum, Fin.sum_univ_succAbove _ i, lt_irrefl, if_false, smul_add]
  exact add_comm _ _

omit [Fintype ι] in
private theorem after {n : ℕ} (i : Fin (n + 1)) (x w : Fin (n + 1) → E) :
    mixedSum (i.val+1) x w = base i x w + (Real.sqrt n)⁻¹ • x i := by
  simp only [mixedSum, base, normalizedSum, Fin.sum_univ_succAbove _ i,
    Nat.lt_succ_self, if_true, smul_add]
  rw [add_comm]
  congr 2
  apply Finset.sum_congr rfl
  intro k _
  rcases lt_or_gt_of_ne (Fin.succAbove_ne i k) with h | h
  · simp [h, show (i.succAbove k).val < i.val + 1 from Nat.lt_succ_of_lt h]
  · simp [not_lt_of_ge h.le, show ¬(i.succAbove k).val < i.val + 1 from Nat.not_lt.mpr h]

omit [Fintype ι] in
private theorem zero_mixed {n : ℕ} (x w : Fin (n + 1) → E) :
    mixedSum 0 x w = (Real.sqrt n)⁻¹ • ∑ j, w j := by simp [mixedSum]

omit [Fintype ι] in
private theorem full_mixed {n : ℕ} (x w : Fin (n + 1) → E) :
    mixedSum (n + 1) x w = (Real.sqrt n)⁻¹ • ∑ j, x j := by
  simp only [mixedSum, Fin.is_lt, if_true]

omit [Fintype ι] in
private theorem mixed_update {n : ℕ} (i : Fin (n + 1)) (x w : Fin (n + 1) → E) (v : E) :
    mixedSum i.val x (Function.update w i v) = base i x w + (Real.sqrt n)⁻¹ • v := by
  rw [before, Function.update_self]
  congr 1
  unfold base
  apply congrArg (normalizedSum n)
  funext k
  simp

omit [Fintype ι] in
private theorem base_before {n : ℕ} (i : Fin (n + 1)) (x y w : Fin (n + 1) → E)
    (h : ∀ k, k < i → x k = y k) : base i x w = base i y w := by
  unfold base
  apply congrArg (normalizedSum n)
  funext k
  by_cases hk : i.succAbove k < i <;> simp [hk, h]

private theorem measurable_mixed {n : ℕ} (k : ℕ) :
    Measurable (Function.uncurry (mixedSum (ι := ι) (n := n) k)) := by
  unfold Function.uncurry mixedSum
  have hterm (j : Fin (n + 1)) : Measurable
      (fun z : (Fin (n + 1) → E) × (Fin (n + 1) → E) =>
        if j.val < k then z.1 j else z.2 j) := by
    split_ifs <;> fun_prop
  exact (show Measurable (fun _ : (Fin (n + 1) → E) × (Fin (n + 1) → E) => (Real.sqrt n)⁻¹)
    from measurable_const).smul (Finset.measurable_fun_sum Finset.univ fun i _ => hterm i)

private theorem measurable_base {n : ℕ} (i : Fin (n + 1)) :
    Measurable (Function.uncurry (base (ι := ι) i)) := by
  unfold Function.uncurry base normalizedSum
  have hterm (k : Fin n) : Measurable
      (fun z : (Fin (n + 1) → E) × (Fin (n + 1) → E) =>
        if i.succAbove k < i then z.1 (i.succAbove k) else z.2 (i.succAbove k)) := by
    split_ifs <;> fun_prop
  exact (show Measurable (fun _ : (Fin (n + 1) → E) × (Fin (n + 1) → E) => (Real.sqrt n)⁻¹)
    from measurable_const).smul (Finset.measurable_fun_sum Finset.univ fun k _ => hterm k)


private theorem lipschitz_memLp {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] {f : Z → E} (hf : MemLp f 2 μ)
    {T : E → E} {K : ℝ≥0} (hT : LipschitzWith K T) :
    MemLp (fun z => T (f z)) 2 μ := by
  have hTc : LipschitzWith K (fun x => T x - T 0) := LipschitzWith.of_dist_le_mul fun x y => by
    simpa only [dist_sub_right] using hT.dist_le_mul x y
  have h := hTc.comp_memLp (sub_self _) hf
  exact (memLp_congr_ae (g := fun z => T (f z)) (ae_of_all _ fun z => sub_add_cancel (T (f z)) (T 0))).mp (h.add (memLp_const (T 0)))

private theorem mixed_memLp_right {n : ℕ} (k : ℕ) (x : Fin (n + 1) → E) :
    MemLp (fun w => mixedSum k x w) 2 (Measure.pi fun _ => stdGaussian E) := by
  have hcoord (j : Fin (n + 1)) :
      MemLp (fun w : Fin (n + 1) → E => if j.val < k then x j else w j) 2
        (Measure.pi fun _ => stdGaussian E) := by
    by_cases hj : j.val < k
    · simpa only [if_pos hj] using (memLp_const (x j) (p := 2)
        (μ := Measure.pi fun _ : Fin (n + 1) => stdGaussian E))
    · simp only [if_neg hj]
      exact (IsGaussian.memLp_two_id (μ := stdGaussian E)).comp_measurePreserving
        (measurePreserving_eval (fun _ : Fin (n + 1) => stdGaussian E) j)
  exact (memLp_finsetSum Finset.univ (fun j _ => hcoord j)).const_smul ((Real.sqrt n)⁻¹)

private theorem base_memLp_right {n : ℕ} (i : Fin (n + 1)) (x : Fin (n + 1) → E) :
    MemLp (fun w => base i x w) 2 (Measure.pi fun _ => stdGaussian E) := by
  have hcoord (j : Fin n) :
      MemLp (fun w : Fin (n + 1) → E =>
        if i.succAbove j < i then x (i.succAbove j) else w (i.succAbove j)) 2
        (Measure.pi fun _ => stdGaussian E) := by
    by_cases hj : i.succAbove j < i
    · simpa only [if_pos hj] using (memLp_const (x (i.succAbove j)) (p := 2)
        (μ := Measure.pi fun _ : Fin (n + 1) => stdGaussian E))
    · simp only [if_neg hj]
      exact (IsGaussian.memLp_two_id (μ := stdGaussian E)).comp_measurePreserving
        (measurePreserving_eval (fun _ : Fin (n + 1) => stdGaussian E) _)
  exact (memLp_finsetSum Finset.univ (fun j _ => hcoord j)).const_smul ((Real.sqrt n)⁻¹)


/-- Product law of n+1 independent standard Gaussian draws. -/
abbrev paths (ι : Type*) [Fintype ι] (n : ℕ) :=
  Measure.pi fun _ : Fin (n + 1) => stdGaussian (EuclideanSpace ℝ ι)

/-- Conditional mean after the first k draws have been revealed. -/
private def revealed {n : ℕ} (T : E → E) (k : ℕ) (x : Fin (n + 1) → E) : E :=
  ∫ w, T (mixedSum k x w) ∂paths ι n

private def gradient {n : ℕ} (T : E → E) (i : Fin (n + 1)) (x : Fin (n + 1) → E) : E →L[ℝ] E :=
  ∫ w, fderiv ℝ T (base i x w) ∂paths ι n

private theorem revealed_measurable {n : ℕ} {T : E → E} (hT : LipschitzWith 2 T) (k : ℕ) :
    Measurable (revealed (n := n) T k) := by
  exact ((hT.continuous.measurable.comp (measurable_mixed k)).stronglyMeasurable.integral_prod_right'
    (ν := paths ι n)).measurable

private theorem gradient_measurable {n : ℕ} (T : E → E) (i : Fin (n + 1)) :
    Measurable (gradient T i) := by
  exact (((measurable_fderiv ℝ T).comp (measurable_base i)).stronglyMeasurable.integral_prod_right'
    (ν := paths ι n)).measurable

private theorem gradient_bound {n : ℕ} {T : E → E} (hT : LipschitzWith 2 T)
    (i : Fin (n + 1)) (x : Fin (n + 1) → E) : ‖gradient T i x‖ ≤ 2 := by
  have hb (w : Fin (n + 1) → E) : ‖fderiv ℝ T (base i x w)‖ ≤ 2 :=
    norm_fderiv_le_of_lipschitz ℝ hT
  simpa [gradient] using norm_integral_le_of_norm_le_const (μ := paths ι n) (ae_of_all _ hb)

private theorem gradient_before {n : ℕ} (T : E → E) (i : Fin (n + 1)) (x y : Fin (n + 1) → E)
    (h : ∀ k, k < i → x k = y k) : gradient T i x = gradient T i y := by
  unfold gradient
  simp only [base_before i x y _ h]

private theorem revealed_integrable {n : ℕ} {T : E → E} (hT : LipschitzWith 2 T)
    (k : ℕ) (x : Fin (n + 1) → E) :
    Integrable (fun w => T (mixedSum k x w)) (paths ι n) :=
  (lipschitz_memLp _ (mixed_memLp_right k x) hT).integrable (by norm_num)


private theorem expected_after {n : ℕ} {T : E → E} (hT : LipschitzWith 2 T)
    (i : Fin (n + 1)) (x : Fin (n + 1) → E) :
    (∫ g, ∫ w, T (base i x w + (Real.sqrt n)⁻¹ • g) ∂paths ι n ∂stdGaussian E) =
      revealed T i.val x := by
  let P := paths ι n
  let γ := stdGaussian E
  let u (p : E × (Fin (n + 1) → E)) := Function.update p.2 i p.1
  have hu : MeasurePreserving u (γ.prod P) P := fresh_update_preserving γ i
  let F (w : Fin (n + 1) → E) := T (mixedSum i.val x w)
  have hf : Integrable F P := revealed_integrable hT i.val x
  have hcomp : Integrable (fun p => F (u p)) (γ.prod P) := hu.integrable_comp_of_integrable hf
  change _ = ∫ w, F w ∂P
  calc
    _ = ∫ p, F (u p) ∂γ.prod P := by
      rw [integral_prod (fun p => F (u p)) hcomp]
      simp only [F, u, mixed_update, P, γ]
    _ = _ := by
      calc
        _ = ∫ w, F w ∂(γ.prod P).map u := by
          apply (integral_map hu.measurable.aemeasurable _).symm
          rw [hu.map_eq]
          exact hf.aestronglyMeasurable
        _ = _ := by rw [hu.map_eq]

omit [Fintype ι] in
private theorem base_update {n : ℕ} (i : Fin (n + 1)) (x w : Fin (n + 1) → E) (g : E) :
    base i (Function.update x i g) w = base i x w :=
  base_before _ _ _ _ (fun _ hk => Function.update_of_ne hk.ne _ _)

private theorem revealed_next {n : ℕ} (T : E → E)
    (i : Fin (n + 1)) (x : Fin (n + 1) → E) (g : E) :
    revealed T (i.val + 1) (Function.update x i g) =
      ∫ w, T (base i x w + (Real.sqrt n)⁻¹ • g) ∂paths ι n := by
  simp only [revealed, after, base_update, Function.update_self]

private theorem revealed_before {n : ℕ} (T : E → E) (i : Fin (n + 1))
    (x y : Fin (n + 1) → E) (h : ∀ k, k < i → x k = y k) :
    revealed T i.val x = revealed T i.val y := by
  simp only [revealed, before, base_before i x y _ h]


private theorem next_integrable {n : ℕ} {T : E → E} (hT : LipschitzWith 2 T)
    (i : Fin (n + 1)) (x : Fin (n + 1) → E) :
    Integrable (fun g => ∫ w, T (base i x w + (Real.sqrt n)⁻¹ • g) ∂paths ι n)
      (stdGaussian E) := by
  have h := (fresh_update_preserving (stdGaussian E) i).integrable_comp_of_integrable
    (revealed_integrable hT i.val x)
  have h' : Integrable (fun p : E × (Fin (n + 1) → E) =>
      T (mixedSum i.val x (Function.update p.2 i p.1))) ((stdGaussian E).prod (paths ι n)) := h
  simpa only [mixed_update] using h'.integral_prod_left

/-- Error after one Gaussian coordinate is revealed, relative to its averaged linear term. -/
def incrementError {n : ℕ} (T : E → E) (i : Fin (n + 1)) (x : Fin (n + 1) → E) : E :=
  revealed T (i.val + 1) x - revealed T i.val x -
    (Real.sqrt n)⁻¹ • gradient T i x (x i)

private theorem error_update {n : ℕ} (T : E → E) (i : Fin (n + 1)) (x : Fin (n + 1) → E) (g : E) :
    incrementError T i (Function.update x i g) =
      (∫ w, T (base i x w + (Real.sqrt n)⁻¹ • g) ∂paths ι n) -
        revealed T i.val x - (Real.sqrt n)⁻¹ • gradient T i x g := by
  have hp : ∀ k, k < i → Function.update x i g k = x k :=
    fun _ h => Function.update_of_ne h.ne _ _
  simp only [incrementError, revealed_next, revealed_before T i _ x hp,
    gradient_before T i _ x hp, Function.update_self]

/-- The linearization error averages to zero in the newly revealed coordinate,
for every value of the other coordinates. -/
theorem increment_centered {n : ℕ} {T : E → E} (hT : LipschitzWith 2 T)
    (i : Fin (n + 1)) (x : Fin (n + 1) → E) :
    (∫ g, incrementError T i (Function.update x i g) ∂stdGaussian E) = 0 := by
  have hid : Integrable (id : E → E) (stdGaussian E) := IsGaussian.memLp_two_id.integrable (by norm_num)
  have hg : Integrable (fun g => (gradient T i x) g) (stdGaussian E) :=
    (gradient T i x).integrable_comp hid
  have hmean : (∫ g, (gradient T i x) g ∂stdGaussian E) = 0 := by
    rw [(gradient T i x).integral_comp_id_comm hid, integral_id_stdGaussian, map_zero]
  have hleft : Integrable (fun g => (∫ w, T (base i x w + (Real.sqrt n)⁻¹ • g) ∂paths ι n) -
      revealed T i.val x) (stdGaussian E) := (next_integrable hT i x).sub (integrable_const _)
  have hright : Integrable (fun g => (Real.sqrt n)⁻¹ • gradient T i x g) (stdGaussian E) :=
    hg.smul ((Real.sqrt n : ℝ)⁻¹)
  simp only [error_update]
  rw [integral_sub hleft hright, integral_sub (next_integrable hT i x) (integrable_const (revealed T i.val x)),
    expected_after hT, integral_const, probReal_univ, one_smul, sub_self, integral_smul, hmean]
  simp

open Green54GaussianLinearization

private theorem increment_integrable_update {n : ℕ} {T : E → E} (hT : LipschitzWith 2 T)
    (i : Fin (n + 1)) (x : Fin (n + 1) → E) :
    Integrable (fun g => incrementError T i (Function.update x i g)) (stdGaussian E) := by
  simp only [error_update]
  apply ((next_integrable hT i x).sub (integrable_const _)).sub
  have hid : Integrable (id : E → E) (stdGaussian E) :=
    IsGaussian.memLp_two_id.integrable (by norm_num)
  exact ((gradient T i x).integrable_comp hid).smul ((Real.sqrt n : ℝ)⁻¹)

private def remainder {n : ℕ} (T : E → E) (i : Fin (n + 1)) (x : Fin (n + 1) → E)
    (z : E × (Fin (n + 1) → E)) : E :=
  (Real.sqrt n)⁻¹ • slopeError T (Real.sqrt n)⁻¹ (base i x z.2, z.1)

private theorem remainder_bound {n : ℕ} {T : E → E} (hT : LipschitzWith 2 T)
    (i : Fin (n + 1)) (x : Fin (n + 1) → E) (z : E × (Fin (n + 1) → E)) :
    ‖remainder T i x z‖ ≤ (‖(Real.sqrt n : ℝ)⁻¹‖ * 4) * ‖z.1‖ := by
  rw [remainder, norm_smul, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hb := slopeError_bound hT (Real.sqrt n)⁻¹ (base i x z.2,z.1)
  norm_num at hb
  exact hb

private theorem remainder_memLp {n : ℕ} {T : E → E} (hT : LipschitzWith 2 T)
    (i : Fin (n + 1)) (x : Fin (n + 1) → E) :
    MemLp (remainder T i x) 2 ((stdGaussian E).prod (paths ι n)) := by
  have hm : Measurable (fun z : E × (Fin (n+1) → E) => (base i x z.2,z.1)) :=
    ((measurable_base i).comp (measurable_const.prodMk measurable_snd)).prodMk measurable_fst
  have hRm : Measurable (remainder T i x) :=
    (measurable_const (a := (Real.sqrt n : ℝ)⁻¹)).smul
      ((measurable_slopeError hT (Real.sqrt n)⁻¹).comp hm)
  have hG := (IsGaussian.memLp_two_id (μ := stdGaussian E)).norm.comp_measurePreserving
    (measurePreserving_fst (ν := paths ι n))
  exact (hG.const_mul (‖(Real.sqrt n : ℝ)⁻¹‖ * 4)).mono' hRm.aestronglyMeasurable
    (ae_of_all _ (remainder_bound hT i x))

set_option maxHeartbeats 800000 in
private theorem averaged_remainder {n : ℕ} {T : E → E} (hT : LipschitzWith 2 T)
    (i : Fin (n + 1)) (x : Fin (n + 1) → E) (g : E) :
    (∫ w, remainder T i x (g,w) ∂paths ι n) =
      incrementError T i (Function.update x i g) +
        (revealed T i.val x - ∫ w, T (base i x w) ∂paths ι n) := by
  let P := paths ι n
  have hm : Measurable (base i x) := (measurable_base (ι := ι) i).comp
    (measurable_prodMk_left (x := x))
  have hbase : Integrable (fun w => T (base i x w)) P :=
    (lipschitz_memLp _ (base_memLp_right i x) hT).integrable (by norm_num)
  have hlp : MemLp (fun w => base i x w + (Real.sqrt n)⁻¹ • g) 2 P :=
    (base_memLp_right i x).add (memLp_const ((Real.sqrt n)⁻¹ • g))
  have hshift : Integrable (fun w => T (base i x w + (Real.sqrt n)⁻¹ • g)) P :=
    (lipschitz_memLp _ hlp hT).integrable (by norm_num)
  have hder : Integrable (fun w => fderiv ℝ T (base i x w)) P :=
    (integrable_const (2 : ℝ)).mono' ((measurable_fderiv ℝ T).comp hm).aestronglyMeasurable
      (ae_of_all _ fun _ => norm_fderiv_le_of_lipschitz ℝ hT)
  have heval : Integrable (fun w => fderiv ℝ T (base i x w) g) P :=
    (ContinuousLinearMap.apply ℝ E g).integrable_comp hder
  have hleft : Integrable (fun w => T (base i x w + (Real.sqrt n)⁻¹ • g) - T (base i x w))
      (paths ι n) := hshift.sub hbase
  have hright : Integrable (fun w => (Real.sqrt n)⁻¹ • fderiv ℝ T (base i x w) g)
      (paths ι n) := heval.smul ((Real.sqrt n : ℝ)⁻¹)
  simp only [remainder, scaled_slopeError, error_update]
  rw [integral_sub hleft hright,
    integral_sub hshift hbase, integral_smul, ← ContinuousLinearMap.integral_apply hder]
  unfold gradient
  abel

private theorem fiber_error_energy {n : ℕ} {T : E → E} (hT : LipschitzWith 2 T)
    (i : Fin (n + 1)) (x : Fin (n + 1) → E) :
    (∫ g, ‖incrementError T i (Function.update x i g)‖ ^ 2 ∂stdGaussian E) ≤
      ∫ z, ‖remainder T i x z‖ ^ 2 ∂(stdGaussian E).prod (paths ι n) := by
  have h := conditional_error_energy (stdGaussian E) (paths ι n)
    (remainder T i x) (remainder_memLp hT i x)
  dsimp only at h
  simp only [averaged_remainder hT i x,
    integral_add (increment_integrable_update hT i x) (integrable_const _),
    increment_centered hT, zero_add, integral_const, probReal_univ, one_smul,
    add_sub_cancel_right] at h
  exact h

private theorem increment_measurable {n : ℕ} {T : E → E} (hT : LipschitzWith 2 T)
    (i : Fin (n + 1)) : Measurable (incrementError T i) := by
  have hD : Measurable (fun x : Fin (n + 1) → E => gradient T i x (x i)) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp
      ((gradient_measurable T i).prodMk (measurable_pi_apply i))
  exact ((revealed_measurable hT (i.val + 1)).sub (revealed_measurable hT i.val)).sub
    ((measurable_const (a := (Real.sqrt n : ℝ)⁻¹)).smul hD)

private theorem increment_memLp {n : ℕ} {T : E → E} (hT : LipschitzWith 2 T) (i : Fin (n+1)) :
    MemLp (incrementError T i) 2 (paths ι n) := by
  let γ := stdGaussian E
  let K := ‖(Real.sqrt n : ℝ)⁻¹‖ * 4
  let b := ∫ g, K * ‖g‖ ∂γ
  have hg : Integrable (fun g : E => K * ‖g‖) γ :=
    (IsGaussian.memLp_two_id (μ := γ)).norm.integrable (by norm_num) |>.const_mul K
  have hi := (IsGaussian.memLp_two_id (μ := γ)).norm.comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin (n+1) => γ) i)
  apply ((hi.const_mul K).add (memLp_const b)).mono' (increment_measurable hT i).aestronglyMeasurable
  apply ae_of_all
  intro x
  let F (g : E) := ∫ w, remainder T i x (g,w) ∂paths ι n
  have hF (g : E) : ‖F g‖ ≤ K * ‖g‖ := by
    simpa only [probReal_univ, one_smul, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := paths ι n)
        (ae_of_all _ fun w => remainder_bound hT i x (g,w)))
  have hmean : ‖∫ g, F g ∂γ‖ ≤ b := norm_integral_le_of_norm_le hg (ae_of_all _ hF)
  have heq : F (x i) - (∫ g, F g ∂γ) = incrementError T i x := by
    simp only [F, averaged_remainder hT, γ, integral_add (increment_integrable_update hT i x)
      (integrable_const _), increment_centered hT, zero_add, integral_const, probReal_univ,
      one_smul, add_sub_cancel_right, Function.update_eq_self]
  rw [← heq]
  exact (norm_sub_le _ _).trans (add_le_add (hF _) hmean)

private theorem integral_preserved {V W H : Type*} [MeasurableSpace V] [MeasurableSpace W]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {μ : Measure V} {ν : Measure W} {f : V → W} (hf : MeasurePreserving f μ ν)
    {G : W → H} (hG : AEStronglyMeasurable G ν) :
    (∫ v, G (f v) ∂μ) = ∫ w, G w ∂ν := by
  calc
    _ = ∫ w, G w ∂μ.map f := (integral_map hf.measurable.aemeasurable (hf.map_eq.symm ▸ hG)).symm
    _ = _ := by rw [hf.map_eq]

/-- The one-step mean square error is bounded by the Gaussian directional remainder
at step size (1/√n), times its squared step size. -/
theorem increment_energy_le {n : ℕ} (hn : 0 < n) {T : E → E} (hT : LipschitzWith 2 T)
    (i : Fin (n+1)) :
    (∫ x, ‖incrementError T i x‖ ^ 2 ∂paths ι n) ≤
      (Real.sqrt n)⁻¹ ^ 2 * ∫ z, ‖slopeError T (Real.sqrt n)⁻¹ z‖ ^ 2
        ∂(stdGaussian E).prod (stdGaussian E) := by
  let γ := stdGaussian E
  let P := paths ι n
  let c := (Real.sqrt n : ℝ)⁻¹
  let G (z : E × E) := ‖c • slopeError T c z‖ ^ 2
  have hGm : Measurable G := ((measurable_const (a := c)).smul
    (measurable_slopeError hT c)).norm.pow_const 2
  have hGs : MemLp (fun z : E × E => c • slopeError T c z) 2 (γ.prod γ) := by
    have hid := (IsGaussian.memLp_two_id (μ := γ)).norm.comp_measurePreserving
      (measurePreserving_snd (μ := γ))
    apply (hid.const_mul (‖c‖ * 4)).mono'
      ((measurable_const (a := c)).smul (measurable_slopeError hT c)).aestronglyMeasurable
    apply ae_of_all
    intro z
    change ‖c • slopeError T c z‖ ≤ (‖c‖ * 4) * ‖z.2‖
    rw [norm_smul, mul_assoc]
    have hb := slopeError_bound hT c z
    norm_num at hb
    exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
  have hbase : MeasurePreserving (fun z : (Fin (n+1) → E) × (Fin (n+1) → E) => base i z.1 z.2)
      (P.prod P) γ := measurePreserving_fst.comp (spliced_sum_preserving (ι := ι) hn i)
  let v (z : (Fin (n+1) → E) × (E × (Fin (n+1) → E))) := (base i z.1 z.2.2,z.2.1)
  have hv : MeasurePreserving v (P.prod (γ.prod P)) (γ.prod γ) :=
    (hbase.prod (MeasurePreserving.id γ)).comp
      ((measurePreserving_prodAssoc P P γ).symm.comp
        ((MeasurePreserving.id P).prod Measure.measurePreserving_swap))
  let u (z : (Fin (n+1) → E) × E) := Function.update z.1 i z.2
  have hu : MeasurePreserving u (P.prod γ) P :=
    (fresh_update_preserving γ i).comp Measure.measurePreserving_swap
  have hi := hu.integrable_comp_of_integrable (increment_memLp hT i).norm.integrable_sq
  have hj : Integrable (fun z => G (v z)) (P.prod (γ.prod P)) :=
    hv.integrable_comp_of_integrable hGs.norm.integrable_sq
  calc
    _ = ∫ z, ‖incrementError T i (u z)‖ ^ 2 ∂P.prod γ :=
      (integral_preserved hu ((increment_measurable hT i).norm.pow_const 2).aestronglyMeasurable).symm
    _ = ∫ x, ∫ g, ‖incrementError T i (Function.update x i g)‖ ^ 2 ∂γ ∂P :=
      integral_prod _ hi
    _ ≤ ∫ x, ∫ z, ‖remainder T i x z‖ ^ 2 ∂γ.prod P ∂P :=
      integral_mono_ae hi.integral_prod_left hj.integral_prod_left
        (ae_of_all _ (fiber_error_energy hT i))
    _ = ∫ z, G (v z) ∂P.prod (γ.prod P) := (integral_prod _ hj).symm
    _ = ∫ z, G z ∂γ.prod γ := integral_preserved hv hGm.aestronglyMeasurable
    _ = _ := by
      simp only [G, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, integral_const_mul, c, γ]

private theorem increment_past {n : ℕ} (T : E → E) (i : Fin (n+1)) (x y : Fin (n+1) → E)
    (h : ∀ k, k ≤ i → x k = y k) : incrementError T i x = incrementError T i y := by
  have h' : ∀ k, k < i → x k = y k := fun k hk => h k hk.le
  have hnext (w : Fin (n+1) → E) : mixedSum (i.val+1) x w = mixedSum (i.val+1) y w := by
    simp only [after, base_before i x y w h', h i le_rfl]
  have hr : revealed T (i.val+1) x = revealed T (i.val+1) y := by
    simp only [revealed, hnext]
  simp only [incrementError, hr, revealed_before T i x y h', gradient_before T i x y h',
    h i le_rfl]

set_option maxHeartbeats 800000 in
/-- Orthogonality adds the per-step Gaussian errors without a loss of a factor of n. -/
theorem path_energy_le {n : ℕ} (hn : 0 < n) {T : E → E} (hT : LipschitzWith 2 T) :
    (∫ x, ‖∑ i : Fin (n+1), incrementError T i x‖ ^ 2 ∂paths ι n) ≤
      ((n : ℝ) + 1) * (Real.sqrt n)⁻¹ ^ 2 * ∫ z, ‖slopeError T (Real.sqrt n)⁻¹ z‖ ^ 2
        ∂(stdGaussian E).prod (stdGaussian E) := by
  have hu (i : Fin (n+1)) (w : Fin n → E) (g : E) :
      Function.update (Fin.insertNth (α := fun _ => E) i 0 w) i g =
        Fin.insertNth (α := fun _ => E) i g w :=
    Fin.update_insertNth (α := fun _ : Fin (n+1) => E) i 0 g w
  have heq (i : Fin (n+1)) (w : Fin n → E) :
      (fun g => incrementError T i (Fin.insertNth (α := fun _ => E) i g w)) =
      (fun g => incrementError T i (Function.update (Fin.insertNth (α := fun _ => E) i 0 w) i g)) :=
    funext fun g => congrArg (incrementError T i) (hu i w g).symm
  have hfi (i : Fin (n+1)) (w : Fin n → E) :
      Integrable (fun g => incrementError T i (Fin.insertNth (α := fun _ => E) i g w)) (stdGaussian E) := by
    rw [heq]
    exact increment_integrable_update hT i _
  have hzero (i : Fin (n+1)) (w : Fin n → E) :
      (∫ g, incrementError T i (Fin.insertNth (α := fun _ => E) i g w) ∂stdGaussian E) = 0 := by
    rw [heq]
    exact increment_centered hT i _
  have he := adapted_sum_energy (stdGaussian E) (incrementError T) (increment_memLp hT)
    (increment_past T) hfi hzero
  rw [he]
  calc
    _ ≤ ∑ _i : Fin (n+1), ((Real.sqrt n)⁻¹ ^ 2 * ∫ z, ‖slopeError T (Real.sqrt n)⁻¹ z‖ ^ 2
        ∂(stdGaussian E).prod (stdGaussian E)) :=
      Finset.sum_le_sum fun i _ => increment_energy_le hn hT i
    _ = _ := by simp [mul_assoc]

/-- The error of the entire martingale approximation vanishes in Gaussian mean square. -/
theorem path_energy_tendsto {T : E → E} (hT : LipschitzWith 2 T) :
    Filter.Tendsto (fun n : ℕ => ∫ x, ‖∑ i : Fin (n+1), incrementError T i x‖ ^ 2 ∂paths ι n)
      Filter.atTop (nhds 0) := by
  have ht : Filter.Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) Filter.atTop (nhdsWithin 0 {0}ᶜ) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop, ?_⟩
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    exact inv_ne_zero (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn))
  have hl := (mean_square_slopes hT).comp ht
  have h2 := (tendsto_const_nhds (x := (2 : ℝ))).mul hl
  have hb : ∀ᶠ n : ℕ in Filter.atTop,
      (∫ x, ‖∑ i : Fin (n+1), incrementError T i x‖ ^ 2 ∂paths ι n) ≤
        2 * ∫ z, ‖slopeError T (Real.sqrt n)⁻¹ z‖ ^ 2 ∂(stdGaussian E).prod (stdGaussian E) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    apply (path_energy_le hn hT).trans
    apply mul_le_mul_of_nonneg_right _ (integral_nonneg fun _ => sq_nonneg _)
    rw [inv_pow, Real.sq_sqrt (by positivity), ← div_eq_mul_inv]
    apply (div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).mpr
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n from hn)
    linarith
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ =>
    integral_nonneg (fun _ => sq_nonneg _)) hb (by simpa [Function.comp_def] using h2)

private def fillPast {n : ℕ} (i : Fin (n+1)) (u : Fin i.val → E) (j : Fin (n+1)) : E :=
  if hj : j.val < i.val then u ⟨j.val,hj⟩ else 0

/-- The predictable contraction at each step is half the expected derivative over
the remaining independent Gaussian coordinates. -/
def coefficient {n : ℕ} (T : E → E) (i : Fin (n+1)) (u : Fin i.val → E) : E →L[ℝ] E :=
  (2 : ℝ)⁻¹ • gradient T i (fillPast i u)

theorem coefficient_measurable {n : ℕ} (T : E → E) (i : Fin (n+1)) :
    Measurable (coefficient T i) := by
  have hm : Measurable (fillPast (ι := ι) i) := by
    apply measurable_pi_lambda _ fun j => ?_
    unfold fillPast
    split_ifs <;> fun_prop
  exact (measurable_const (a := (2 : ℝ)⁻¹)).smul ((gradient_measurable T i).comp hm)

theorem coefficient_contraction {n : ℕ} {T : E → E} (hT : LipschitzWith 2 T) (i : Fin (n+1))
    (u : Fin i.val → E) : ‖coefficient T i u‖ ≤ 1 := by
  rw [coefficient, norm_smul, Real.norm_of_nonneg (by norm_num)]
  linarith [gradient_bound hT i (fillPast i u)]

private theorem sum_error {n : ℕ} (T : E → E) (x : Fin (n+1) → E) :
    (∑ i, incrementError T i x) =
      T ((Real.sqrt n)⁻¹ • ∑ i, x i) - (∫ w, T ((Real.sqrt n)⁻¹ • ∑ i, w i) ∂paths ι n) -
      (Real.sqrt n)⁻¹ • ∑ i, gradient T i x (x i) := by
  have htel := (Fin.sum_univ_eq_sum_range
    (fun k => revealed T (k+1) x - revealed T k x) (n+1)).trans
    (Finset.sum_range_sub (fun k => revealed T k x) (n+1))
  simp only [incrementError, Finset.sum_sub_distrib, ← Finset.smul_sum]
  rw [← Finset.sum_sub_distrib, htel]
  simp only [revealed, full_mixed, zero_mixed, integral_const, probReal_univ, one_smul]

private theorem contracted_eq {n : ℕ} (T : E → E) (x : Fin (n+1) → E) :
    contractedSum (coefficient T) x =
      (Real.sqrt (n+1 : ℕ))⁻¹ • (2 : ℝ)⁻¹ • ∑ i, gradient T i x (x i) := by
  change _ • ∑ i : Fin (n+1), coefficient T i (fun j => x ⟨j.val,j.isLt.trans i.isLt⟩) (x i) = _
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hp : ∀ k, k < i → fillPast i (fun j => x ⟨j.val,j.isLt.trans i.isLt⟩) k = x k := by
    intro k hk
    simp [fillPast, show k.val < i.val from hk]
  simp [coefficient, gradient_before T i _ x hp]

/-- The ratio between the leave-one-out and full-path square-root normalizations. -/
def scale (n : ℕ) : ℝ := Real.sqrt n / Real.sqrt (n+1 : ℕ)

theorem scale_tendsto : Filter.Tendsto scale Filter.atTop (nhds 1) := by
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp (tendsto_natCast_div_add_atTop (1 : ℝ))
  simp only [Function.comp_def, Real.sqrt_one, Real.sqrt_div (Nat.cast_nonneg _)] at h
  change Filter.Tendsto (fun n : ℕ => Real.sqrt n / Real.sqrt (n+1 : ℕ)) _ _
  simpa only [Nat.cast_add, Nat.cast_one] using h

omit [Fintype ι] in
private theorem scale_inv_sum {n : ℕ} (hn : 0 < n) (x : Fin (n+1) → E) :
    (scale n)⁻¹ • normalizedSum (n+1) x = (Real.sqrt n)⁻¹ • ∑ i, x i := by
  unfold scale normalizedSum
  rw [smul_smul]
  congr 1
  have h₁ : Real.sqrt (n+1 : ℕ) ≠ 0 := by positivity
  have h₀ : Real.sqrt n ≠ 0 := by positivity
  field_simp

/-- Smooth rescaling of the centered Lipschitz image on a single standard Gaussian space. -/
def profile (T : E → E) (n : ℕ) (z : E) : E :=
  (scale n / 2) • (T ((scale n)⁻¹ • z) - ∫ w, T ((scale n)⁻¹ • w) ∂stdGaussian E)

theorem profile_measurable {T : E → E} (hT : LipschitzWith 2 T) (n : ℕ) :
    Measurable (profile T n) := by
  have hTm := hT.continuous.measurable
  unfold profile
  fun_prop

theorem contracted_measurable {n : ℕ} (T : E → E) :
    Measurable (contractedSum (coefficient (n := n) T)) := by
  have hterm (i : Fin (n+1)) : Measurable (fun x : Fin (n+1) → E => gradient T i x (x i)) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp
      ((gradient_measurable T i).prodMk (measurable_pi_apply i))
  simp_rw [show contractedSum (coefficient (n := n) T) = _ from funext (contracted_eq T)]
  exact (measurable_const (a := (Real.sqrt (n+1 : ℕ))⁻¹)).smul
    ((measurable_const (a := (2 : ℝ)⁻¹)).smul (Finset.measurable_fun_sum Finset.univ fun i _ => hterm i))

/-- Coupling a finite adapted sum to the centered Lipschitz image of the normalized path sum. -/
theorem profile_sub_contracted {n : ℕ} (hn : 0 < n) {T : E → E} (hT : LipschitzWith 2 T)
    (x : Fin (n+1) → E) :
    profile T n (normalizedSum (n+1) x) - contractedSum (coefficient T) x =
      (scale n / 2) • ∑ i, incrementError T i x := by
  have hZ := normalizedSum_preserving (ι := ι) (Nat.succ_pos n)
  have hm : Measurable (fun w : E => T ((scale n)⁻¹ • w)) :=
    hT.continuous.measurable.comp ((measurable_const (a := (scale n)⁻¹)).smul measurable_id)
  have hi := integral_preserved hZ hm.aestronglyMeasurable
  simp only [scale_inv_sum hn] at hi
  have hscalar : (Real.sqrt (n+1 : ℕ))⁻¹ * (2 : ℝ)⁻¹ = scale n / 2 * (Real.sqrt n)⁻¹ := by
    unfold scale
    have h₁ : Real.sqrt (n+1 : ℕ) ≠ 0 := by positivity
    have h₀ : Real.sqrt n ≠ 0 := by positivity
    field_simp
  simp only [profile, scale_inv_sum hn, ← hi, contracted_eq, sum_error, smul_sub, smul_smul, hscalar]

/-- The accumulated linearization error is square integrable on every finite path space. -/
theorem path_error_memLp {n : ℕ} {T : E → E} (hT : LipschitzWith 2 T) :
    MemLp (fun x => ∑ i : Fin (n+1), incrementError T i x) 2 (paths ι n) :=
  memLp_finsetSum Finset.univ fun i _ => increment_memLp hT i

/-- The expected distance in the path coupling tends to zero. -/
theorem mean_coupling_error_tendsto {T : E → E} (hT : LipschitzWith 2 T) :
    Filter.Tendsto (fun n : ℕ => ∫ x, ‖profile T n (normalizedSum (n+1) x) -
      contractedSum (coefficient T) x‖ ∂paths ι n) Filter.atTop (nhds 0) := by
  have hs (n : ℕ) : MemLp (fun x => ∑ i : Fin (n+1), incrementError T i x) 2 (paths ι n) :=
    path_error_memLp hT
  have hmean := (Real.continuous_sqrt.continuousAt.tendsto.comp (path_energy_tendsto hT))
  have h₀ : Filter.Tendsto (fun n : ℕ => ∫ x, ‖∑ i : Fin (n+1), incrementError T i x‖ ∂paths ι n)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ => integral_nonneg fun _ => norm_nonneg _)
      (Filter.Eventually.of_forall fun n => Real.le_sqrt_of_sq_le ?_)
    · simpa only [Function.comp_def, Real.sqrt_zero] using hmean
    · simpa only [Real.norm_eq_abs, sq_abs] using mean_energy_le (hs n).norm
  have hl := ((scale_tendsto.div_const (2 : ℝ)).norm.mul h₀)
  apply Filter.Tendsto.congr' _ (by simpa using hl)
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  simp only [profile_sub_contracted hn hT, norm_smul, integral_const_mul]
  norm_num [Real.norm_eq_abs, abs_div]

#print axioms scale_tendsto
#print axioms profile_measurable
#print axioms contracted_measurable
#print axioms profile_sub_contracted
#print axioms path_error_memLp
#print axioms mean_coupling_error_tendsto

#print axioms coefficient_measurable
#print axioms coefficient_contraction
#print axioms increment_centered
#print axioms increment_energy_le
#print axioms path_energy_le
#print axioms path_energy_tendsto

end Green54GaussianApproximation
