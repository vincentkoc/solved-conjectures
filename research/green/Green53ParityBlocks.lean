import Mathlib

/-! # Counting disjoint sign changes in an affine parity slice -/

open Finset
open scoped Classical
namespace Green53ParityBlocks

/-- In a two-point fibre differing by one heavy sign, at least one weighted
sum has absolute value at least as large as that coefficient. -/
theorem one_large_sign (a b : ℝ) : |a| ≤ |b+a| ∨ |a| ≤ |b-a| := by
  by_contra! h
  have triangle := abs_sub (b+a) (b-a)
  rw [show b+a-(b-a)=2*a by ring,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at triangle
  linarith

/-- If the mean is at least half the block count, a variance bound controls the
fraction of samples with fewer than one quarter of the blocks. -/
theorem few_good {m : ℕ} {Sample : Type*} [Fintype Sample] (score : Sample → ℝ) (μ : ℝ)
    (mean : (m:ℝ)/2 ≤ μ)
    (variance : ∑ x, (score x-μ)^2 ≤ Fintype.card Sample * ((m:ℝ)/4))
    (pos : 0 < m) :
    ((univ.filter (fun x => score x < (m:ℝ)/4)).card:ℝ) * m ≤ 4*Fintype.card Sample := by
  classical
  let bad := univ.filter (fun x => score x < (m:ℝ)/4)
  have lower (x) (hx : x∈bad) : ((m:ℝ)/4)^2 ≤ (score x-μ)^2 := by
    have sm := (mem_filter.mp hx).2
    change score x < (m:ℝ)/4 at sm
    have pos' : (0:ℝ) ≤ m := Nat.cast_nonneg _
    nlinarith [sq_nonneg ((μ-score x)-(m:ℝ)/4),
      mul_nonneg (by linarith : 0 ≤ μ-score x-(m:ℝ)/4) (by linarith : 0 ≤ μ-score x+(m:ℝ)/4)]
  have I : (bad.card:ℝ)*((m:ℝ)/4)^2 ≤ Fintype.card Sample * ((m:ℝ)/4) := calc
    _ = ∑ _x∈bad, ((m:ℝ)/4)^2 := by simp
    _ ≤ ∑ x∈bad, (score x-μ)^2 := sum_le_sum lower
    _ ≤ ∑ x, (score x-μ)^2 := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; positivity)
    _ ≤ _ := variance
  change (bad.card:ℝ)*(m:ℝ) ≤ _
  have pm : (0:ℝ) < m := by exact_mod_cast pos
  apply (mul_le_mul_iff_left₀ pm).mp
  nlinarith
/-- Sum the diagonal terms of the centered second moment. -/
theorem uncorrelated_variance {I Sample : Type*} [Fintype I] [Fintype Sample]
    (w : I → Sample → ℝ) (μ : I → ℝ)
    (off : ∀ i j, i ≠ j → ∑ x, (w i x-μ i)*(w j x-μ j)=0)
    (diag : ∀ i, ∑ x, (w i x-μ i)^2 ≤ Fintype.card Sample/4) :
    ∑ x, ((∑ i, w i x)-(∑ i, μ i))^2 ≤ Fintype.card Sample*(Fintype.card I/4) := by
  classical
  let f i x := w i x-μ i
  have expand x : ((∑ i, w i x)-(∑ i, μ i))^2 = ∑ i,∑ j, f i x*f j x := by
    rw [←sum_sub_distrib, pow_two, sum_mul_sum]
  have inner (i : I) : (∑ j,∑ x, f i x*f j x)=∑ x,(w i x-μ i)^2 := by
    rw [sum_eq_single i]
    · simp [f,pow_two]
    · intro j _ ne
      exact off i j ne.symm
    · simp
  calc
    _ = ∑ x, ∑ i, ∑ j, f i x*f j x := sum_congr rfl (fun x _ => expand x)
    _ = ∑ i, ∑ j, ∑ x, f i x*f j x := by
      rw [sum_comm]; exact sum_congr rfl (fun _ _ => sum_comm)
    _ = ∑ i, ∑ x,(w i x-μ i)^2 := sum_congr rfl (fun i _ => inner i)
    _ ≤ ∑ _i : I, (Fintype.card Sample:ℝ)/4 := sum_le_sum (fun i _ => diag i)
    _ = _ := by simp; ring


end Green53ParityBlocks

#print axioms Green53ParityBlocks.one_large_sign
#print axioms Green53ParityBlocks.uncorrelated_variance
#print axioms Green53ParityBlocks.few_good
