import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic

/-!
# Finite differences on a set of prime-field steps

The first nonzero positive power sum of the allowed steps determines the
leading degree of their summed difference operator. This is the polynomial
ingredient in the prime-degree permutation argument of Peter Müller.
-/

namespace Erdos478.PrimeDifferences
open Polynomial Finset
open scoped Polynomial
noncomputable section

variable {K : Type*} [Field K]

def moment (U : Finset K) (i : ℕ) := ∑ u ∈ U, u^i

def difference (U : Finset K) (f : K[X]) := ∑ u ∈ U, (taylor u f-f)

theorem difference_eval (U : Finset K) (f : K[X]) (x : K) :
    (difference U f).eval x = ∑ u ∈ U, (f.eval (x+u)-f.eval x) := by
  simp [difference,eval_finsetSum,taylor_eval,eval_sub]

theorem difference_degree (U : Finset K) (f : K[X]) : (difference U f).natDegree≤f.natDegree := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  simpa only [natDegree_taylor,max_self] using (natDegree_sub_le (taylor i f) f)

private theorem sum_values (U : Finset K) (f : K[X]) {n : ℕ} (hd : f.natDegree<n) :
    ∑ u ∈ U, f.eval u=∑ i ∈ range n, f.coeff i*moment U i := by
  simp_rw [eval_eq_sum_range' hd]
  rw [sum_comm]
  simp only [moment,mul_sum]

private theorem constant_part (U : Finset K) (f : K[X]) {n : ℕ} (hd : f.natDegree<n) :
    (∑ u ∈ U, f.eval u)-U.card*f.coeff 0 =
      ∑ i ∈ (range n).erase 0, f.coeff i*moment U i := by
  rw [sum_values U f hd]
  have h := sum_erase_add (range n) (fun i => f.coeff i*moment U i) (show 0∈range n from mem_range.mpr (by omega))
  rw [← h]
  simp [moment,mul_comm]

theorem difference_coeff (U : Finset K) (f : K[X]) {n : ℕ} (hd : f.natDegree<n) (j : ℕ) :
    (difference U f).coeff j=∑ i ∈ (range n).erase 0, ((i+j).choose j:K)*f.coeff (i+j)*moment U i := by
  have h := constant_part U (hasseDeriv j f) ((natDegree_hasseDeriv_le f j).trans_lt (by omega : f.natDegree-j<n))
  simp only [hasseDeriv_coeff,zero_add,Nat.choose_self,Nat.cast_one,one_mul] at h
  simpa [difference,finsetSum_coeff,coeff_sub,taylor_coeff,sum_sub_distrib] using h

variable {p : ℕ} [Fact p.Prime]

private theorem cast_choose_ne {n k : ℕ} (hn : n<p) (hk : k≤n) : (n.choose k : ZMod p)≠0 := by
  intro he
  have hdiv := (ZMod.natCast_eq_zero_iff _ _).mp he
  have hfac : p∣n.factorial := by
    rw [← Nat.choose_mul_factorial_mul_factorial hk]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hdiv _) _
  exact hn.not_ge ((Fact.out : p.Prime).dvd_factorial.mp hfac)

theorem difference_leading {U : Finset (ZMod p)} {k : ℕ} (hk : 0<k) (hM : moment U k≠0)
    (hsmall : ∀ i, 0 < i → i < k → moment U i=0) {f : (ZMod p)[X]}
    (hdeg : k≤f.natDegree) (hp : f.natDegree<p) :
    (difference U f).coeff (f.natDegree-k)≠0 := by
  let j := f.natDegree-k
  have hkj : k+j=f.natDegree := by dsimp [j]; omega
  rw [difference_coeff U f hp,Finset.sum_eq_single k]
  · rw [show k+(f.natDegree-k)=f.natDegree from hkj,coeff_natDegree]
    exact mul_ne_zero (mul_ne_zero (cast_choose_ne hp (by omega))
      (leadingCoeff_ne_zero.mpr (by intro h; simp [h] at hdeg; omega))) hM
  · intro i hi hik
    obtain ⟨hi₀,_⟩ := mem_erase.mp hi
    rcases lt_or_gt_of_ne hik with h | h
    · rw [hsmall i (by omega) h,mul_zero]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < i+(f.natDegree-k)),mul_zero,zero_mul]
  · simp [mem_erase,hk.ne',mem_range,hdeg.trans_lt hp]

/-- Some positive moment at most the number of nonzero steps is nonzero. -/
theorem exists_moment {U : Finset (ZMod p)} (hU : U.Nonempty) (h0 : 0∉U) (hp : U.card<p) :
    ∃ k, 0<k ∧ k≤U.card ∧ moment U k≠0 := by
  classical
  let f : (ZMod p)[X] := ∏ u ∈ U, (X-C u)
  have hd : f.natDegree=U.card := by simp [f]
  have hval (u : ZMod p) (hu : u∈U) : f.eval u=0 := by
    simp only [f,eval_prod,eval_sub,eval_X,eval_C,Finset.prod_eq_zero_iff]
    exact ⟨u,hu,sub_self _⟩
  have hcoeff : f.coeff 0≠0 := by
    rw [coeff_zero_eq_eval_zero]
    simp only [f,eval_prod,eval_sub,eval_X,eval_C,zero_sub,Finset.prod_ne_zero_iff,neg_ne_zero]
    exact fun x hx h => h0 (h ▸ hx)
  by_contra! h
  have hs := constant_part U f (by omega : f.natDegree<U.card+1)
  rw [Finset.sum_eq_zero (fun u hu => hval u hu)] at hs
  have hz : ∀ i ∈ (range (U.card+1)).erase 0, f.coeff i*moment U i=0 := by
    intro i hi
    obtain ⟨hi,hu⟩ := mem_erase.mp hi
    rw [h i (by omega) (by have := mem_range.mp hu; omega),mul_zero]
  rw [sum_eq_zero hz,zero_sub,neg_eq_zero,mul_eq_zero] at hs
  rcases hs with he | he
  · exact hp.not_ge (Nat.le_of_dvd (card_pos.mpr hU) ((ZMod.natCast_eq_zero_iff _ _).mp he))
  · exact hcoeff he

#print axioms difference_eval
#print axioms difference_degree
#print axioms difference_coeff
#print axioms difference_leading
#print axioms exists_moment
end
end Erdos478.PrimeDifferences
