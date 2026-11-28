import CunninghamLinearReciprocalRoots

/-! A unit-leading reciprocal factor of a balanced Jones iterate would force an integral trace. -/

namespace CunninghamChain.LinearRoots
open Polynomial

private lemma integral_root {A : ℤ[X]} (hu : IsUnit A.leadingCoeff) {z : ℂ}
    (h : aeval z A=0) : IsIntegral ℤ z := by
  rcases Int.isUnit_iff.mp hu with hp|hm
  · exact ⟨A,hp,h⟩
  · refine ⟨-A,?_,?_⟩
    · show (-A).leadingCoeff=1
      rw [leadingCoeff_neg,hm]; decide
    · change aeval z (-A)=0
      simp [h]

private lemma trace_obstruction {a : ℤ} (ha : 4 ≤ a) (k : Bool) {z : ℂ}
    (hz : z≠0) (hint : IsIntegral ℤ (z+z⁻¹))
    (hq : a*(sign k+a)*(z^2+1) - 2*a^2*z=0) : False := by
  let q : ℚ := 2*(a:ℚ)/(a+sign k)
  have den : ((a:ℂ)+(sign k:ℂ))≠0 := by
    exact_mod_cast (show a+sign k≠0 by cases k <;> simp [sign] <;> omega)
  have he : (algebraMap ℚ ℂ q)=z+z⁻¹ := by
    change (q:ℂ)=_
    dsimp [q]
    push_cast
    field_simp [den,hz]
    have ha0 : (a:ℂ)≠0 := by exact_mod_cast (by omega : a≠0)
    apply mul_left_cancel₀ ha0
    linear_combination -hq
  have iq : IsIntegral ℤ q := (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp (he ▸ hint)
  obtain ⟨t,ht⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral iq
  have qt : (t:ℚ)=2*(a:ℚ)/(a+sign k) := ht
  have di : (a:ℚ)+(sign k:ℚ)≠0 := by
    exact_mod_cast (show a+sign k≠0 by cases k <;> simp [sign] <;> omega)
  have hdiv : a+sign k ∣ 2*(sign k) := by
    have eq : t*(a+sign k)=2*a := by exact_mod_cast (eq_div_iff di).mp qt
    exact ⟨2-t,by linear_combination eq⟩
  have le := Int.natAbs_dvd_natAbs.mpr hdiv
  cases k <;> norm_num [sign] at le <;>
    have bound := Nat.le_of_dvd (by decide : 0<2) le <;> omega

private lemma balanced_at_one (k : Bool) (a : ℕ) (n : ℕ) :
    aeval (1:ℂ) (term k a (-a) n)=(sign k:ℂ)*n := by
  induction n with
  | zero => simp [term,polynomialTerm]
  | succ n ih => rw [term_step,ih]; push_cast; ring

/-- At coefficient at least four, a nonconstant rational factor with integral
unit endpoints cannot be invariant under signed reversal. -/
theorem no_reciprocal_unit_factor {a : ℕ} (ha : 4 ≤ a) (k : Bool) {n : ℕ} (hn : 0<n)
    {A : ℤ[X]} (hd : 0<A.natDegree) (hu : IsUnit A.leadingCoeff) (hv : IsUnit (A.coeff 0))
    (hf : A ∣ polynomialTerm k (C (a:ℤ)*X+C (-(a:ℤ))) n)
    (symm : A = C (A.leadingCoeff*A.coeff 0)*A.reverse) : False := by
  have ne : A≠0 := leadingCoeff_ne_zero.mp hu.ne_zero
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ A (by
    rw [degree_eq_natDegree ne]; exact_mod_cast (by omega : A.natDegree≠0))
  have z0 : z≠0 := by
    rintro rfl
    have hz' : (A.coeff 0 : ℂ)=0 := by simpa [aeval_def,←eval_map,←coeff_zero_eq_eval_zero] using hz
    exact hv.ne_zero (Int.cast_eq_zero.mp hz')
  let : Invertible z := invertibleOfNonzero z0
  have ir : aeval z⁻¹ A.reverse=0 := by
    simpa only [aeval_def,invOf_eq_inv] using
      (eval₂_reverse_eq_zero_iff (algebraMap ℤ ℂ) z A).mpr hz
  have hi : aeval z⁻¹ A=0 := by
    calc _ = aeval z⁻¹ (C (A.leadingCoeff*A.coeff 0)*A.reverse) := congrArg _ symm
         _ = 0 := by rw [map_mul,ir,mul_zero]
  have root (x : ℂ) (hr : aeval x A=0) : aeval x (term k a (-a) n)=0 := by
    have comp : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = algebraMap ℤ ℂ := Subsingleton.elim _ _
    have h := (aeval_dvd (x:=x) hf)
    rw [hr,zero_dvd_iff] at h
    simpa only [term,aeval_def,eval₂_map,comp] using h
  have zr := root z hz
  have z1 : z≠1 := by
    rintro rfl
    rw [balanced_at_one] at zr
    cases k <;> simp [sign,hn.ne'] at zr
  have quad := reciprocal_root_equation z0 z1 zr (root _ hi)
  push_cast at quad
  apply trace_obstruction (a:=(a:ℤ)) (by omega) k z0 ((integral_root hu hz).add (integral_root hu hi))
  linear_combination quad

#print axioms no_reciprocal_unit_factor

end CunninghamChain.LinearRoots
