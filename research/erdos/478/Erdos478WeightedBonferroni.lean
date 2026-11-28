import Mathlib

/-!
# Weighted Bonferroni inequalities

For independent forbidden events with probabilities in the unit interval, the
odd and even partial inclusion-exclusion sums bracket the surviving density.
The indicator-valued specialization also applies pointwise in an interval.
-/

namespace Erdos478.SchurSieve
open Finset

variable {ι : Type*}

noncomputable def moment (Q : Finset ι) (u : ι → ℝ) (j : ℕ) : ℝ :=
  ∑ T ∈ Q.powersetCard j, ∏ i ∈ T, u i

noncomputable def partialMass (Q : Finset ι) (u : ι → ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ range (m+1), (-1 : ℝ)^j * moment Q u j

@[simp] private theorem moment_zero (Q : Finset ι) (u : ι → ℝ) : moment Q u 0 = 1 := by
  simp [moment]

private theorem moment_insert [DecidableEq ι] {q : ι} {Q : Finset ι} (hq : q ∉ Q)
    (u : ι → ℝ) (j : ℕ) :
    moment (insert q Q) u (j+1) = moment Q u (j+1) + u q * moment Q u j := by
  classical
  have absent {T : Finset ι} {k : ℕ} (h : T ∈ Q.powersetCard k) : q ∉ T :=
    fun hx => hq ((mem_powersetCard.mp h).1 hx)
  unfold moment
  rw [powersetCard_succ_insert hq,sum_union,mul_sum,sum_image]
  · congr 1
    exact sum_congr rfl fun T hT => prod_insert (absent hT)
  · intro T hT S hS h
    simpa [absent hT,absent hS] using congrArg (fun A : Finset ι => A.erase q) h
  · apply disjoint_left.mpr
    intro T hT him
    obtain ⟨S,hS,rfl⟩ := mem_image.mp him
    exact absent hT (mem_insert_self ..)

theorem partialMass_succ (Q : Finset ι) (u : ι → ℝ) (m : ℕ) :
    partialMass Q u (m+1) = partialMass Q u m + (-1:ℝ)^(m+1)*moment Q u (m+1) := by
  simp only [partialMass,sum_range_succ]

private theorem partialMass_insert [DecidableEq ι] {q : ι} {Q : Finset ι} (hq : q ∉ Q)
    (u : ι → ℝ) (m : ℕ) :
    partialMass (insert q Q) u (m+1) = partialMass Q u (m+1) - u q * partialMass Q u m := by
  induction m with
  | zero =>
    rw [partialMass_succ,partialMass_succ,moment_insert hq]
    simp [partialMass]
    ring
  | succ m ih =>
    rw [partialMass_succ,ih,moment_insert hq,partialMass_succ Q u (m+1),
      partialMass_succ Q u m,pow_succ (-(1:ℝ)) (m+1)]
    ring

/-- Bonferroni's two bounds for arbitrary weights between zero and one. -/
theorem weighted_bonferroni (Q : Finset ι) (u : ι → ℝ)
    (hu : ∀ q ∈ Q, 0 ≤ u q ∧ u q ≤ 1) (r : ℕ) :
    partialMass Q u (2*r+1) ≤ ∏ q ∈ Q, (1-u q) ∧
      (∏ q ∈ Q, (1-u q)) ≤ partialMass Q u (2*r) := by
  classical
  induction Q using Finset.induction_on generalizing r with
  | empty =>
    have h (m : ℕ) : partialMass (∅ : Finset ι) u m = 1 := by
      unfold partialMass
      rw [sum_eq_single 0]
      · simp
      · intro j _ hj
        obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
        simp [moment,powersetCard_eq_empty.mpr (show (∅ : Finset ι).card < i+1 by simp)]
      · simp
    simp [h]
  | @insert q Q hq ih =>
    have hQ := fun i (hi : i ∈ Q) => hu i (mem_insert_of_mem hi)
    obtain ⟨hq0,hq1⟩ := hu q (mem_insert_self ..)
    rw [prod_insert hq,partialMass_insert hq]
    constructor
    · obtain ⟨hl,he⟩ := ih hQ r
      nlinarith only [hl,mul_le_mul_of_nonneg_left he hq0]
    · cases r with
      | zero =>
        have hP : (∏ i ∈ Q, (1-u i)) ≤ 1 :=
          prod_le_one (fun i hi => sub_nonneg.mpr (hQ i hi).2) (fun i hi => by linarith [(hQ i hi).1])
        have hP0 := prod_nonneg (s := Q) (fun i hi => sub_nonneg.mpr (hQ i hi).2)
        simpa [partialMass] using (mul_le_mul_of_nonneg_right (by linarith : 1-u q ≤ 1) hP0).trans
          (by simpa using hP)
      | succ r =>
        rw [show 2*(r+1) = (2*r+1)+1 by omega,partialMass_insert hq]
        have hl := (ih hQ r).1
        have he := (ih hQ (r+1)).2
        rw [show 2*(r+1)=(2*r+1)+1 by omega] at he
        nlinarith only [he,mul_le_mul_of_nonneg_left hl hq0]

#print axioms weighted_bonferroni

end Erdos478.SchurSieve
