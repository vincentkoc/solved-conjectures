import Green33ReflectionRigidity
import Green33Divergence

/-! Ordered representation tails inside subsets of asymptotically thin cyclic two-bases. -/

open Finset Filter Green33Multiplicity Green33ReflectionRigidity Green33TailEnergy
open scoped Pointwise Topology

namespace Green33HereditaryTail

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

private lemma pointwise (b a d M : ℕ) (hba : b ≤ a) (hcov : 2 ≤ a + d) :
    ((b : ℝ) - 1) * (b - 2 : ℝ) ≤ (if M < b then (b : ℝ)^2 else 0) +
      M * (a + d - 2 : ℝ) + 2 - b := by
  have he : (2 : ℝ) ≤ a + d := by exact_mod_cast hcov
  have hb : (b : ℝ) ≤ a := by exact_mod_cast hba
  have hM : 0 ≤ (M : ℝ) := Nat.cast_nonneg _
  have hbn : 0 ≤ (b : ℝ) := Nat.cast_nonneg _
  have hdn : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  split_ifs with ht
  · nlinarith [mul_nonneg hM (sub_nonneg.mpr he)]
  · have hcut : (b : ℝ) ≤ M := by exact_mod_cast Nat.le_of_not_gt ht
    nlinarith [mul_nonneg (sub_nonneg.mpr hcut) (sub_nonneg.mpr he),
      mul_nonneg hbn (sub_nonneg.mpr hb), mul_nonneg hbn hdn]

/-- The energy above a cutoff is measured inside `B` itself. Only its superset
`A` must cover the group. -/
theorem subset_tail_bound (A B : Finset G) (hA : A + A = univ) (hBA : B ⊆ A) (M : ℕ) :
    2 * (B.card : ℝ)^2 - 3 * B.card + 2 - 2 * Fintype.card G ≤
      (tailEnergy B M : ℝ) + M * ((A.card : ℝ)^2 + A.card - 2 * Fintype.card G) := by
  have hr (C : Finset G) : ∑ s, (reps C s : ℝ) = (C.card : ℝ)^2 := by
    exact_mod_cast (show ∑ s, reps C s = C.card ^ 2 by
      simpa [reps, sq] using sum_card_fiberwise_eq_card_filter
        (C ×ˢ C) univ (fun t : G × G => t.1 + t.2))
  have hd : ∑ s, (diagonalReps A s : ℝ) = A.card := by
    exact_mod_cast (show ∑ s, diagonalReps A s = A.card by
      simpa [diagonalReps] using sum_card_fiberwise_eq_card_filter A univ (fun a => a + a))
  have ht : ∑ s, (if M < reps B s then (reps B s : ℝ)^2 else 0) = (tailEnergy B M : ℝ) := by
    simp [tailEnergy, sum_filter]
  have hb (s : G) : reps B s ≤ reps A s :=
    card_le_card (filter_subset_filter _ (product_subset_product hBA hBA))
  have hh := (polynomial_floor B).trans (sum_le_sum (s := univ) fun s _ =>
    pointwise _ _ _ M (hb s) (cover_counts_le A hA s).2)
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, hr, hd, ht, sum_const, card_univ,
    nsmul_eq_mul] at hh
  nlinarith only [hh]

/-- A uniform lower bound on the normalized tail of every subset of relative size
at least `α`, allowing a varying cutoff whose normalized surplus cost vanishes. -/
theorem eventually_all_subset_tails_of_cost {ι : Type*} {l : Filter ι} (q : ι → ℕ+)
    (A : (i : ι) → Finset (ZMod (q i))) (M : ι → ℕ)
    (hq : Tendsto (fun i => (q i : ℕ)) l atTop) (hA : ∀ i, A i + A i = univ)
    (hd : Tendsto (fun i => ((A i).card : ℝ) / Real.sqrt (q i)) l (𝓝 (Real.sqrt 2)))
    (hcost : Tendsto (fun i => (M i : ℝ) *
      ((((A i).card : ℝ)^2 + (A i).card) / (q i : ℝ) - 2)) l (𝓝 0))
    {α c : ℝ} (hα : 0 ≤ α) (hc : c < 2 * α^2 - 2) :
    ∀ᶠ i in l, ∀ B ⊆ A i, α * Real.sqrt (q i) ≤ (B.card : ℝ) →
      c < (tailEnergy B (M i) : ℝ) / (q i : ℝ) := by
  obtain ⟨hlin, _⟩ := card_limits q (fun i => (A i).card) hq hd
  have hs := (hlin.const_mul 3).add hcost
  norm_num at hs
  filter_upwards [hs.eventually_lt_const (show 0 < 2 * α^2 - 2 - c by linarith)] with i hi
  intro B hBA hb
  have hqpos : 0 < (q i : ℝ) := by exact_mod_cast (q i).pos
  have hsq := pow_le_pow_left₀ (mul_nonneg hα (Real.sqrt_nonneg _)) hb 2
  rw [mul_pow, Real.sq_sqrt hqpos.le] at hsq
  have hbk : (B.card : ℝ) ≤ (A i).card := by exact_mod_cast card_le_card hBA
  have hf := subset_tail_bound (A i) B (hA i) hBA (M i)
  rw [ZMod.card] at hf
  field_simp [hqpos.ne'] at hi ⊢
  nlinarith only [hi, hsq, hbk, hf]

/-- For fixed cutoffs the cost condition follows from the size of the ambient basis. -/
theorem eventually_all_subset_tails {ι : Type*} {l : Filter ι} (q : ι → ℕ+)
    (A : (i : ι) → Finset (ZMod (q i)))
    (hq : Tendsto (fun i => (q i : ℕ)) l atTop) (hA : ∀ i, A i + A i = univ)
    (hd : Tendsto (fun i => ((A i).card : ℝ) / Real.sqrt (q i)) l (𝓝 (Real.sqrt 2)))
    (M : ℕ) {α c : ℝ} (hα : 0 ≤ α) (hc : c < 2 * α^2 - 2) :
    ∀ᶠ i in l, ∀ B ⊆ A i, α * Real.sqrt (q i) ≤ (B.card : ℝ) →
      c < (tailEnergy B M : ℝ) / (q i : ℝ) := by
  apply eventually_all_subset_tails_of_cost q A (fun _ => M) hq hA hd _ hα hc
  obtain ⟨hk, hk₂⟩ := card_limits q (fun i => (A i).card) hq hd
  simpa only [add_div, add_zero, sub_self, mul_zero] using
    (((hk₂.add hk).sub (tendsto_const_nhds (x := (2 : ℝ)))).const_mul (M : ℝ))

/-- After arbitrary deletions leaving at least `α√q` points with `α > 1`,
the maximum ordered count inside the surviving subset exceeds any fixed cap. -/
theorem eventually_all_subset_maxima {ι : Type*} {l : Filter ι} (q : ι → ℕ+)
    (A : (i : ι) → Finset (ZMod (q i)))
    (hq : Tendsto (fun i => (q i : ℕ)) l atTop) (hA : ∀ i, A i + A i = univ)
    (hd : Tendsto (fun i => ((A i).card : ℝ) / Real.sqrt (q i)) l (𝓝 (Real.sqrt 2)))
    (M : ℕ) {α : ℝ} (hα : 1 < α) :
    ∀ᶠ i in l, ∀ B ⊆ A i, α * Real.sqrt (q i) ≤ (B.card : ℝ) → M < maxReps B := by
  have hc : 0 < 2 * α^2 - 2 := by nlinarith [sq_nonneg (α - 1)]
  filter_upwards [eventually_all_subset_tails q A hq hA hd M (by linarith : 0 ≤ α) hc]
    with i hi
  intro B hBA hb
  have ht := hi B hBA hb
  by_contra! hcap
  have hs (s : ZMod (q i)) : ¬M < reps B s :=
    not_lt.mpr ((le_sup (f := reps B) (mem_univ s)).trans hcap)
  simp [tailEnergy, hs] at ht

#print axioms subset_tail_bound
#print axioms eventually_all_subset_tails_of_cost
#print axioms eventually_all_subset_tails
#print axioms eventually_all_subset_maxima

end Green33HereditaryTail
