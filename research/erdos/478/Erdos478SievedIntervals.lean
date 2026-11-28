import Erdos478WeightedBonferroni
import CunninghamBrunSieve

/-!
# A finite lower sieve for polynomial values

Compare odd inclusion-exclusion in an interval with the model in which the
local residues are independent. Each intersection costs at most one endpoint
per CRT class. The first omitted comparison with an even sum controls the tail.
-/

namespace Erdos478.SchurSieve
open Finset

variable (B : (q : ℕ) → Finset (ZMod q))

noncomputable def density (q : ℕ) : ℝ := ((B q).card : ℝ)/q

private noncomputable def indicator (x q : ℕ) : ℝ := by
  classical exact if (x : ZMod q) ∈ B q then 1 else 0

noncomputable def survivors (N : ℕ) (Q : Finset ℕ) : Finset ℕ := by
  classical exact (range N).filter fun x => ∀ q ∈ Q, (x : ZMod q) ∉ B q

private theorem product_indicators (x : ℕ) (T : Finset ℕ) :
    ∏ q ∈ T, indicator B x q = if ∀ q ∈ T, (x : ZMod q) ∈ B q then 1 else 0 := by
  classical
  split_ifs with h
  · exact prod_eq_one fun q hq => if_pos (h q hq)
  · push Not at h
    obtain ⟨q,hq,h⟩ := h
    exact prod_eq_zero hq (if_neg h)

private theorem count_survivors (N : ℕ) (Q : Finset ℕ) :
    (∑ x ∈ range N, ∏ q ∈ Q, (1-indicator B x q)) = ((survivors B N Q).card : ℝ) := by
  classical
  have h (x : ℕ) : (∏ q ∈ Q, (1-indicator B x q)) =
      if ∀ q ∈ Q, (x : ZMod q) ∉ B q then 1 else 0 := by
    split_ifs with hx
    · exact prod_eq_one fun q hq => by simp [indicator,hx q hq]
    · push Not at hx
      obtain ⟨q,hq,hx⟩ := hx
      exact prod_eq_zero hq (by simp [indicator,hx])
  simp only [h,← sum_filter]
  simp [survivors]

private theorem moment_error (N : ℕ) (Q : Finset ℕ) (hp : ∀ q ∈ Q, q.Prime) (j : ℕ) :
    |(∑ x ∈ range N, moment Q (indicator B x) j) - N * moment Q (density B) j| ≤
      ∑ T ∈ Q.powersetCard j, ∏ q ∈ T, ((B q).card : ℝ) := by
  classical
  unfold moment
  rw [sum_comm,mul_sum,← sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  apply sum_le_sum
  intro T hT
  simp only [product_indicators,← sum_filter,sum_const,nsmul_eq_mul,mul_one]
  exact (CunninghamChain.sieve_residue_intersection_count N T
    (fun q hq => hp q ((mem_powersetCard.mp hT).1 hq)) B).1

private theorem partial_error (N : ℕ) (Q : Finset ℕ) (hp : ∀ q ∈ Q, q.Prime) (m : ℕ) :
    |(∑ x ∈ range N, partialMass Q (indicator B x) m) - N * partialMass Q (density B) m| ≤
      ∑ j ∈ range (m+1), ∑ T ∈ Q.powersetCard j, ∏ q ∈ T, ((B q).card : ℝ) := by
  classical
  unfold partialMass
  rw [sum_comm,mul_sum,← sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  apply sum_le_sum
  intro j _
  rw [← mul_sum,mul_left_comm (N:ℝ),← mul_sub,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
  exact moment_error B N Q hp j

/-- The surviving count is at least the independent density minus an odd
symmetric tail and the accumulated CRT discrepancy. -/
theorem finite_lower (N : ℕ) (Q : Finset ℕ) (hp : ∀ q ∈ Q, q.Prime)
    (hu : ∀ q ∈ Q, 0 ≤ density B q ∧ density B q ≤ 1) (r : ℕ) :
    (N:ℝ)*((∏ q ∈ Q, (1-density B q)) - moment Q (density B) (2*r+1)) -
      (∑ j ∈ range (2*r+2), ∑ T ∈ Q.powersetCard j, ∏ q ∈ T, ((B q).card : ℝ)) ≤
        ((survivors B N Q).card : ℝ) := by
  classical
  have hmodel := (weighted_bonferroni Q _ hu r).2
  have hind (x q : ℕ) : 0 ≤ indicator B x q ∧ indicator B x q ≤ 1 := by
    unfold indicator; split <;> norm_num
  have hsample := sum_le_sum (s := range N) fun x _ =>
    (weighted_bonferroni Q _ (fun q _ => hind x q) r).1
  rw [count_survivors] at hsample
  have herr := (abs_le.mp (partial_error B N Q hp (2*r+1))).1
  have hnext := partialMass_succ Q (density B) (2*r)
  simp only [pow_add,pow_mul,neg_one_sq,one_pow,pow_one,mul_neg_one,neg_mul,one_mul] at hnext
  linarith only [hsample,herr,hnext,mul_le_mul_of_nonneg_left hmodel (Nat.cast_nonneg N),
    congrArg (fun t : ℝ => (N:ℝ)*t) hnext]

#print axioms finite_lower

end Erdos478.SchurSieve
