import Mathlib

/-! Eisenstein binomials for the second Jones chain at a square coefficient. -/

namespace CunninghamChain.GapLift
open Polynomial

/-- A simple rational zero of A makes S^d + A(T) Eisenstein in ℚ[T][S]. -/
theorem binomial_of_simple_root {A : ℚ[X]} {r : ℚ} (root : A.eval r=0)
    (simple : A.derivative.eval r ≠ 0) {d : ℕ} (hd : 0 < d) :
    Irreducible ((X : (ℚ[X])[X])^d + C A) := by
  let P : Ideal ℚ[X] := Ideal.span {X-C r}
  have prime : P.IsPrime := Ideal.isPrime_span_singleton_of_prime (prime_X_sub_C r)
  have mon : ((X : (ℚ[X])[X])^d+C A).Monic := monic_X_pow_add_C A hd.ne'
  have div : X-C r ∣ A := dvd_iff_isRoot.mpr root
  have square : ¬(X-C r)^2 ∣ A := by
    rintro ⟨H,eq⟩
    apply simple
    rw [eq,derivative_mul,derivative_X_sub_C_sq]
    simp
  apply IsEisensteinAt.irreducible (𝓟:=P) _ prime mon.isPrimitive
    (by simpa only [natDegree_X_pow_add_C] using hd)
  constructor
  · rw [mon.leadingCoeff]
    exact (Ideal.ne_top_iff_one P).mp prime.ne_top
  · intro j hj
    rw [natDegree_X_pow_add_C] at hj
    rw [coeff_add,coeff_X_pow,if_neg hj.ne,zero_add,coeff_C]
    split
    · exact Ideal.mem_span_singleton.mpr div
    · exact P.zero_mem
  · rw [coeff_add,coeff_X_pow,if_neg (by omega),zero_add,coeff_C_zero]
    change A ∉ Ideal.span {X-C r}^2
    simpa only [Ideal.span_singleton_pow,Ideal.mem_span_singleton] using square

/-- The second-kind endpoint with square coefficient b² has a simple zero
at 1+1/b even after multiplication by any power of T. -/
theorem square_endpoint_binomial {b : ℚ} (hb : 1 < b) (m : ℕ) {d : ℕ} (hd : 0 < d) :
    Irreducible ((X : (ℚ[X])[X])^d+C ((X:ℚ[X])^m*(C (b^2)*(X-1)^2-1))) := by
  let r := 1+1/b
  have br : b*(r-1)=1 := by dsimp [r]; field_simp; ring
  have nz : r ≠ 0 := by dsimp [r]; positivity
  have zero : b^2*(r-1)^2-1=0 := by nlinarith [congrArg (·^2) br]
  apply binomial_of_simple_root (r:=r) _ _ hd
  · simp [zero]
  · rw [derivative_mul]
    simp [derivative_sub,derivative_mul,derivative_pow,zero]
    exact ⟨fun h => (nz h).elim,by linarith,fun h => by simp [h] at br⟩

#print axioms binomial_of_simple_root
#print axioms square_endpoint_binomial

end CunninghamChain.GapLift
