import Green54GaussianContractions
import Mathlib.MeasureTheory.Integral.Prod

/-! Coordinate replacement and orthogonality for finite Gaussian product measures. -/

noncomputable section
open MeasureTheory ProbabilityTheory Green54Contractions
open scoped RealInnerProductSpace
namespace Green54GaussianResampling

private theorem splice_preserving {ι V : Type*} [Fintype ι] [MeasurableSpace V]
    (μ : Measure V) [IsProbabilityMeasure μ] (P : ι → Prop) [DecidablePred P] :
    MeasurePreserving (fun z : (ι → V) × (ι → V) => fun i => if P i then z.1 i else z.2 i)
      ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ)) (Measure.pi fun _ => μ) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => V) P
  have he := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) P
  have H := he.symm.comp ((measurePreserving_fst.comp he).prod (measurePreserving_snd.comp he))
  have heq : (fun z : (ι → V) × (ι → V) => fun i => if P i then z.1 i else z.2 i) =
      e.symm ∘ Prod.map (Prod.fst ∘ e) (Prod.snd ∘ e) := by
    funext z
    apply e.injective
    rw [Function.comp_apply, MeasurableEquiv.apply_symm_apply]
    apply Prod.ext
    · funext i
      exact if_pos i.property
    · funext i
      exact if_neg i.property
  rw [heq]
  exact H

/-- Use earlier draws from the first path and later draws from an independent path.
The normalized sum excluding the current draw is standard Gaussian and independent of it. -/
theorem spliced_sum_preserving {ι : Type*} [Fintype ι] {n : ℕ} (hn : 0 < n) (i : Fin (n + 1)) :
    let E := EuclideanSpace ℝ ι
    let γ := stdGaussian E
    let P := Measure.pi (fun _ : Fin (n + 1) => γ)
    MeasurePreserving (fun z : (Fin (n + 1) → E) × (Fin (n + 1) → E) =>
      (normalizedSum n (fun k => if i.succAbove k < i then z.1 (i.succAbove k)
        else z.2 (i.succAbove k)), z.1 i)) (P.prod P) (γ.prod γ) := by
  dsimp only
  let E := EuclideanSpace ℝ ι
  let γ := stdGaussian E
  have hs := splice_preserving γ (fun k : Fin (n + 1) => k ≤ i)
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => γ) i).comp hs
  have hm := Measure.measurePreserving_swap.comp
    (((MeasurePreserving.id γ).prod (normalizedSum_preserving (ι := ι) hn)).comp he)
  convert hm using 1
  funext z
  apply Prod.ext
  · apply congrArg (normalizedSum n)
    funext k
    change (if i.succAbove k < i then _ else _) = (if i.succAbove k ≤ i then _ else _)
    rcases lt_or_gt_of_ne (Fin.succAbove_ne i k) with h | h
    · simp [h, h.le]
    · simp [not_lt_of_ge h.le, not_le_of_gt h]
  · change z.1 i = (if i ≤ i then z.1 i else z.2 i)
    simp

variable {V F : Type*} [MeasurableSpace V] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F]

/-- Replacing one coordinate of an independent sample by a fresh draw preserves its law. -/
theorem fresh_update_preserving {n : ℕ} (μ : Measure V) [IsProbabilityMeasure μ] (j : Fin (n + 1)) :
    MeasurePreserving (fun p : V × (Fin (n + 1) → V) => Function.update p.2 j p.1)
      (μ.prod (Measure.pi fun _ => μ)) (Measure.pi fun _ => μ) := by
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) j
  have h := he.symm.comp ((MeasurePreserving.id μ).prod (measurePreserving_snd.comp he))
  convert h using 1
  funext p
  exact (Fin.insertNth_removeNth j p.1 p.2).symm

private theorem integral_inner_of_centered_coordinate {n : ℕ} (μ : Measure V) [IsProbabilityMeasure μ]
    (j : Fin (n + 1)) (u v : (Fin (n + 1) → V) → F) (u₀ : (Fin n → V) → F)
    (hu : ∀ y w, u (j.insertNth y w) = u₀ w)
    (hv : ∀ w, Integrable (fun y => v (j.insertNth y w)) μ)
    (hcent : ∀ w, (∫ y, v (j.insertNth y w) ∂μ) = 0)
    (hi : Integrable (fun x => ⟪u x, v x⟫) (Measure.pi fun _ => μ)) :
    (∫ x, ⟪u x, v x⟫ ∂(Measure.pi fun _ => μ)) = 0 := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => V) j
  have he := (measurePreserving_piFinSuccAbove (fun _ => μ) j).symm
  have him := he.integrable_comp_of_integrable hi
  rw [← he.integral_comp' (fun x => ⟪u x, v x⟫), integral_prod_symm (fun z => ⟪u (e.symm z), v (e.symm z)⟫) him]
  have hzero (w : Fin n → V) : (∫ y, ⟪u (e.symm (y,w)), v (e.symm (y,w))⟫ ∂μ) = 0 := by
    change (∫ y, ⟪u (j.insertNth y w), v (j.insertNth y w)⟫ ∂μ) = 0
    simp only [hu, integral_inner (hv w), hcent, inner_zero_right]
  simp only [hzero, integral_zero]

section Energy
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

omit [CompleteSpace F] in
private theorem orthogonal_sum_energy {I : Type*} [Fintype I] [DecidableEq I]
    (d : I → Ω → F) (hd : ∀ i, MemLp (d i) 2 μ)
    (horth : ∀ i j, i ≠ j → (∫ z, ⟪d i z, d j z⟫ ∂μ) = 0) :
    ∫ z, ‖∑ i, d i z‖ ^ 2 ∂μ = ∑ i, ∫ z, ‖d i z‖ ^ 2 ∂μ := by
  have hint (i j : I) : Integrable (fun z => ⟪d i z, d j z⟫) μ :=
    ((hd i).norm.integrable_mul (hd j).norm).mono' ((hd i).aestronglyMeasurable.inner
      (hd j).aestronglyMeasurable) (ae_of_all _ fun z => norm_inner_le_norm _ _)
  have hsq (z : Ω) : ‖∑ i, d i z‖ ^ 2 = ∑ i, ∑ j, ⟪d i z, d j z⟫ := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp only [inner_sum]
  simp_rw [hsq]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hint i j)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hint i j), Finset.sum_eq_single i]
  · simp only [real_inner_self_eq_norm_sq]
  · intro j _ hj
    exact horth _ _ hj.symm
  · simp

end Energy

/-- Centered square-integrable increments on independent coordinates have additive
mean squared norm when each increment only uses coordinates through its own time. -/
theorem adapted_sum_energy {n : ℕ} (μ : Measure V) [IsProbabilityMeasure μ]
    (d : Fin (n + 1) → (Fin (n + 1) → V) → F)
    (hd : ∀ i, MemLp (d i) 2 (Measure.pi fun _ => μ))
    (hpast : ∀ i x y, (∀ k, k ≤ i → x k = y k) → d i x = d i y)
    (hfib : ∀ i w, Integrable (fun y => d i (i.insertNth y w)) μ)
    (hzero : ∀ i w, (∫ y, d i (i.insertNth y w) ∂μ) = 0) :
    ∫ x, ‖∑ i, d i x‖ ^ 2 ∂(Measure.pi fun _ => μ) =
      ∑ i, ∫ x, ‖d i x‖ ^ 2 ∂(Measure.pi fun _ => μ) := by
  let v₀ := Classical.choice (nonempty_of_isProbabilityMeasure μ)
  have hlt (i j : Fin (n + 1)) (hij : i < j) :
      (∫ x, ⟪d i x, d j x⟫ ∂(Measure.pi fun _ => μ)) = 0 := by
    apply integral_inner_of_centered_coordinate μ j (d i) (d j)
      (fun w => d i (j.insertNth v₀ w)) _ (hfib j) (hzero j)
    · exact ((hd i).norm.integrable_mul (hd j).norm).mono' ((hd i).aestronglyMeasurable.inner
        (hd j).aestronglyMeasurable) (ae_of_all _ fun z => norm_inner_le_norm _ _)
    · intro y w
      apply hpast
      intro k hk
      obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq (hk.trans_lt hij).ne
      simp
  apply orthogonal_sum_energy d hd
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt _ _ h
  · simpa only [real_inner_comm (d i _) (d j _)] using hlt j i h


section ConditionalEnergy
variable {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] {μ : Measure Ω} [IsProbabilityMeasure μ]

private theorem square_add_centered (u : H) {r : Ω → H} (hr : MemLp r 2 μ) (hzero : ∫ z, r z ∂μ = 0) :
    ∫ z, ‖u + r z‖ ^ 2 ∂μ = ‖u‖ ^ 2 + ∫ z, ‖r z‖ ^ 2 ∂μ := by
  have hi : Integrable r μ := hr.integrable (by norm_num)
  have hinner : Integrable (fun z => ⟪u, r z⟫) μ := (innerSL ℝ u).integrable_comp hi
  have hs : Integrable (fun z => ‖r z‖ ^ 2) μ := hr.norm.integrable_sq
  have heq (z : Ω) : ‖u + r z‖ ^ 2 = ‖u‖ ^ 2 + 2 * ⟪u, r z⟫ + ‖r z‖ ^ 2 :=
    norm_add_sq_real _ _
  simp only [heq]
  rw [integral_add (f := fun z => ‖u‖ ^ 2 + 2 * ⟪u, r z⟫) ((integrable_const (‖u‖ ^ 2)).add (hinner.const_mul 2)) hs,
    integral_add (integrable_const (‖u‖ ^ 2)) (hinner.const_mul 2), integral_const_mul,
    show ∫ z, ⟪u, r z⟫ ∂μ = 0 by
      rw [show (fun z => ⟪u, r z⟫) = (fun z => (innerSL ℝ u) (r z)) from rfl,
        (innerSL ℝ u).integral_comp_comm hi, hzero, map_zero]]
  simp

private theorem centered_energy {f : Ω → H} (hf : MemLp f 2 μ) :
    (∫ z, ‖f z - ∫ x, f x ∂μ‖ ^ 2 ∂μ) + ‖∫ x, f x ∂μ‖ ^ 2 = ∫ z, ‖f z‖ ^ 2 ∂μ := by
  let m := ∫ x, f x ∂μ
  have hr : MemLp (fun z => f z - m) 2 μ := hf.sub (memLp_const m)
  have h0 : ∫ z, f z - m ∂μ = 0 := by
    rw [integral_sub (hf.integrable (by norm_num)) (integrable_const m)]
    simp [m]
  have h := square_add_centered (μ := μ) m hr h0
  change (∫ z, ‖f z - m‖ ^ 2 ∂μ) + ‖m‖ ^ 2 = _
  simpa only [add_comm m, sub_add_cancel, add_comm (‖m‖ ^ 2)] using h.symm

private theorem mean_energy_le {f : Ω → H} (hf : MemLp f 2 μ) :
    ‖∫ x, f x ∂μ‖ ^ 2 ≤ ∫ z, ‖f z‖ ^ 2 ∂μ := by
  rw [← centered_energy hf]
  exact le_add_of_nonneg_left (integral_nonneg fun _ => sq_nonneg _)

/-- Integrating over a future coordinate and centering in the current coordinate can only
reduce the mean squared error. -/
theorem conditional_error_energy {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
    (ν : Measure V) (τ : Measure W) [IsProbabilityMeasure ν] [IsProbabilityMeasure τ]
    (Q : V × W → H) (hQ : MemLp Q 2 (ν.prod τ)) :
    let F (v : V) := ∫ w, Q (v, w) ∂τ
    (∫ v, ‖F v - ∫ u, F u ∂ν‖ ^ 2 ∂ν) ≤ ∫ z, ‖Q z‖ ^ 2 ∂ν.prod τ := by
  let F (v : V) := ∫ w, Q (v,w) ∂τ
  have hi : Integrable Q (ν.prod τ) := hQ.integrable (by norm_num)
  have hsq : Integrable (fun z => ‖Q z‖ ^ 2) (ν.prod τ) := hQ.norm.integrable_sq
  have hfib : ∀ᵐ v ∂ν, MemLp (fun w => Q (v,w)) 2 τ := by
    filter_upwards [hi.prod_right_ae, hsq.prod_right_ae] with v hv hv'
    exact (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mpr hv'
  have hle : ∀ᵐ v ∂ν, ‖F v‖ ^ 2 ≤ ∫ w, ‖Q (v,w)‖ ^ 2 ∂τ :=
    hfib.mono fun _ hf => mean_energy_le hf
  have hFm : AEStronglyMeasurable F ν := hi.integral_prod_left.aestronglyMeasurable
  have hF2 : Integrable (fun v => ‖F v‖ ^ 2) ν := by
    apply hsq.integral_prod_left.mono' (hFm.norm.pow 2)
    filter_upwards [hle] with v hv
    change ‖‖F v‖ ^ 2‖ ≤ _
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hv
  change (∫ v, ‖F v - ∫ u, F u ∂ν‖ ^ 2 ∂ν) ≤ _
  have hc := centered_energy ((memLp_two_iff_integrable_sq_norm hFm).mpr hF2)
  calc
    _ ≤ ∫ v, ‖F v‖ ^ 2 ∂ν := by linarith [sq_nonneg ‖∫ u, F u ∂ν‖]
    _ ≤ ∫ v, ∫ w, ‖Q (v,w)‖ ^ 2 ∂τ ∂ν := integral_mono_ae hF2 hsq.integral_prod_left hle
    _ = _ := (integral_prod _ hsq).symm

end ConditionalEnergy

#print axioms fresh_update_preserving
#print axioms conditional_error_energy
#print axioms spliced_sum_preserving
#print axioms adapted_sum_energy
end Green54GaussianResampling
