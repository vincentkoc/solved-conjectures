import CunninghamLinearCyclotomicFactors

/-! Reciprocal roots of a balanced Jones iterate would have finite multiplicative order. -/

namespace CunninghamChain.LinearRoots
open Polynomial

/-- At every positive index and every integral a≥2, a nonzero complex number
and its inverse cannot both be roots of the iterate from a(X−1). -/
theorem balanced_no_reciprocal_roots {a : ℤ} (ha : 2≤a) (k : Bool) {n : ℕ}
    (hn : 0<n) {z : ℂ} (hz : z≠0)
    (h : aeval z (term k a (-a) n)=0) (hi : aeval z⁻¹ (term k a (-a) n)=0) : False := by
  have infinite : ¬IsOfFinOrder z := by
    intro finite
    have hd := finite.orderOf_pos
    have dvd := (primitive_dvd hd (IsPrimitiveRoot.orderOf z) _).mpr h
    exact (both_signs_cyclotomic_free_iff a (-a) (by omega)).mpr ⟨ha,rfl⟩ k n _ hn hd dvd
  have h1 : z≠1 := by rintro rfl; exact infinite (isOfFinOrder_iff_pow_eq_one.mpr ⟨1,by decide,by simp⟩)
  let e : ℂ := sign k
  have e0 : e≠0 := by cases k <;> norm_num [e,sign]
  have a0 : (a:ℂ)≠0 := by exact_mod_cast (by omega : a≠0)
  have quad := reciprocal_root_equation hz h1 h hi
  push_cast at quad
  have simple : ((a:ℂ)+e)*(z^2+1)-2*a*z=0 := by
    apply mul_left_cancel₀ a0
    dsimp [e]
    linear_combination quad
  have eq := (root_equation k a (-a) n z h1).mp h
  push_cast at eq
  have p : (z-1)*(a*z-a)+e= -e*z^2 := by linear_combination simple
  change z^n*((z-1)*(a*z+ -a)+e)=e at eq
  rw [←sub_eq_add_neg,p] at eq
  have neg : z^(n+2)= -1 := by
    apply mul_left_cancel₀ e0
    rw [pow_add]
    linear_combination -eq
  exact infinite (isOfFinOrder_iff_pow_eq_one.mpr ⟨(n+2)*2,by omega,by rw [pow_mul,neg]; norm_num⟩)

#print axioms balanced_no_reciprocal_roots

end CunninghamChain.LinearRoots
