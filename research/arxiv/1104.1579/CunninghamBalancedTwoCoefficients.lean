import CunninghamBalancedGapQuadratic
import CunninghamBalancedTwoSearch

/-! Coefficients and correlations of the four-term normalized iterate from 2(X−1). -/

namespace CunninghamChain.BalancedTwo
open Polynomial LinearRoots LargeGap

noncomputable def sparse (k : Bool) (N : ℕ) : ℤ[X] :=
  separated (gapEndpoint 2 k) N

private lemma endpoint (k : Bool) : gapEndpoint 2 k =
    monomial 0 (leading k)+monomial 1 (nextCoeff k)+monomial 2 (thirdCoeff k) := by
  cases k <;> simp [gapEndpoint,gapQuadratic,leading,nextCoeff,thirdCoeff,sign,
    ←C_mul_X_pow_eq_monomial] <;> ring

private lemma reflect_term {i N : ℕ} (h : i≤N) (v : ℤ) :
    reflect N (monomial i v)=monomial (N-i) v := by
  simp only [←C_mul_X_pow_eq_monomial,reflect_C_mul_X_pow,revAt_le h]

lemma sparse_eq (k : Bool) {N : ℕ} (hN : 2≤N) :
    sparse k N=monomial 0 1+monomial N (leading k)+
      monomial (N-1) (nextCoeff k)+monomial (N-2) (thirdCoeff k) := by
  rw [sparse,separated,endpoint,reflect_add,reflect_add,reflect_term (Nat.zero_le _),
    reflect_term (by omega : 1≤N),reflect_term hN]
  simp [add_assoc]

lemma sparse_reflect_eq (k : Bool) (N : ℕ) :
    reflect N (sparse k N)=monomial N 1+monomial 0 (leading k)+
      monomial 1 (nextCoeff k)+monomial 2 (thirdCoeff k) := by
  rw [sparse,separated_reflect,endpoint]
  simp [←C_mul_X_pow_eq_monomial,add_assoc]

lemma sparse_degree (k : Bool) {N : ℕ} (hN : 2≤N) : (sparse k N).natDegree≤N := by
  rw [sparse_eq k hN]
  compute_degree

lemma sparse_at_one (k : Bool) {N : ℕ} (hN : 2≤N) : (sparse k N).eval 1=0 := by
  rw [sparse_eq k hN]
  cases k <;> norm_num [leading,nextCoeff,thirdCoeff,eval_monomial]

lemma at_ends (k : Bool) {N : ℕ} (hN : 3≤N) :
    (sparse k N).coeff 0=1 ∧ (sparse k N).coeff N=leading k := by
  rw [sparse_eq k (by omega)]
  simp [coeff_one,coeff_monomial,show N≠0 by omega,show N-1≠0 by omega,show N-2≠0 by omega,
    show N-1≠N by omega,show N-2≠N by omega]

/-- Below the halfway point only the three endpoint coefficients appear.
At lags zero, one and two the correlations are independent of the degree. -/
theorem sparse_correlation (k : Bool) {N t : ℕ} (hN : 5≤N) (ht : t≤N) :
    (sparse k N*reflect N (sparse k N)).coeff t =
      if t=0 then leading k else if t=1 then nextCoeff k else if t=2 then thirdCoeff k
      else if t=N-2 then lagTwo k else if t=N-1 then lagOne k else if t=N then
        (if k then 30 else 22) else 0 := by
  rw [sparse_reflect_eq,sparse_eq k (by omega)]
  simp only [add_mul,mul_add,monomial_mul_monomial,coeff_add,coeff_monomial,
    Nat.zero_add,Nat.add_zero,one_mul,mul_one,
    show N-2+1=N-1 by omega,show N-2+2=N by omega,show N-1+1=N by omega,
    show N+N≠t by omega,show N-1+N≠t by omega,show N-2+N≠t by omega,
    show N+1≠t by omega,show N+2≠t by omega,show N-1+2≠t by omega,if_false,
    @eq_comm ℕ 0 t,@eq_comm ℕ 1 t,@eq_comm ℕ 2 t,@eq_comm ℕ N t,
    @eq_comm ℕ (N-1) t,@eq_comm ℕ (N-2) t]
  cases k <;> simp only [leading,nextCoeff,thirdCoeff,lagTwo,lagOne,Bool.false_eq_true,
    if_false,if_true] <;> split_ifs <;> omega

#print axioms sparse_correlation

end CunninghamChain.BalancedTwo
