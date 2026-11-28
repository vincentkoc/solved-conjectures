import CunninghamLinearReciprocalRoots
import Mathlib.RingTheory.Polynomial.RationalRoot

/-! Rational roots of the two Jones recurrences from a(X−1). -/

namespace CunninghamChain.LinearRoots
open Polynomial

private theorem reciprocal_of_unit_constant {f : ℤ[X]} {x : ℚ}
    (hu : IsUnit (f.coeff 0)) (hr : aeval x f=0) : ∃ d : ℤ, d≠0 ∧ x=(d:ℚ)⁻¹ := by
  have hn := isUnit_of_dvd_unit (num_dvd_of_is_root hr) hu
  let D : ℤ := IsFractionRing.den ℤ x
  have hd : D≠0 := nonZeroDivisors.coe_ne_zero (IsFractionRing.den ℤ x)
  have he := IsFractionRing.mk'_num_den' ℤ x
  change (IsFractionRing.num ℤ x : ℚ)/(D:ℚ)=x at he
  rcases Int.isUnit_iff.mp hn with h|h
  · exact ⟨D,hd,by simpa [h,one_div] using he.symm⟩
  · exact ⟨-D,neg_ne_zero.mpr hd,by simpa [h,div_eq_mul_inv] using he.symm⟩

/-- Clearing denominators gives an integer test for a specified reciprocal root. -/
theorem scaled_root_iff (k : Bool) (a : ℕ) (n : ℕ) (d : ℤ) (hd : d≠0) (h1 : d≠1) :
    (term k a (-a) n).IsRoot (d:ℚ)⁻¹ ↔
      (a:ℤ)*(d-1)^2 = sign k*d^2*(d^n-1) := by
  have hdC : (d:ℂ)≠0 := by exact_mod_cast hd
  have hn : (d:ℂ)⁻¹≠1 := by
    intro h
    have he : (d:ℂ)=1 := inv_eq_one.mp h
    exact h1 (by exact_mod_cast he)
  let f := term k a (-a) n
  have lift : f.IsRoot (d:ℚ)⁻¹ ↔ aeval ((d:ℂ)⁻¹) f=0 := by
    have e := aeval_algebraMap_apply_eq_algebraMap_eval (A:=ℂ) ((d:ℚ)⁻¹) f
    simpa [IsRoot.def] using (show f.eval (d:ℚ)⁻¹=0 ↔ aeval (algebraMap ℚ ℂ ((d:ℚ)⁻¹)) f=0 by
      rw [e]; exact (map_eq_zero (algebraMap ℚ ℂ)).symm)
  rw [show (term k a (-↑a) n).IsRoot (d:ℚ)⁻¹ ↔ _ from lift,root_equation k a (-a) n _ hn]
  push_cast
  rw [inv_pow]
  constructor
  · intro h
    field_simp [hdC] at h
    exact_mod_cast (show (a:ℂ)*(d-1)^2=(sign k:ℂ)*d^2*(d^n-1) by linear_combination h)
  · intro h
    have e : (a:ℂ)*(d-1)^2=(sign k:ℂ)*d^2*(d^n-1) := by exact_mod_cast h
    field_simp [hdC]
    linear_combination e

/-- The signed denominator and one integer equation characterize all rational roots
at positive indices. The numerator has absolute value one. -/
theorem rational_root_iff_denominator (k : Bool) (a n : ℕ) (ha : 0<a) (hn : 0<n) (x : ℚ) :
    (term k a (-a) n).IsRoot x ↔ ∃ d : ℤ, 2≤d.natAbs ∧ x=(d:ℚ)⁻¹ ∧
      (a:ℤ)*(d-1)^2 = sign k*d^2*(d^n-1) := by
  constructor
  · intro h
    let f := polynomialTerm k (C (a:ℤ)*X + C (-(a:ℤ))) n
    have hr : aeval x f=0 := by simpa [term,IsRoot.def,aeval_def,eval_map,f] using h
    have hu : IsUnit (f.coeff 0) := by
      obtain ⟨i,ei⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
      dsimp [f]; rw [ei]; cases k <;> simp [polynomialTerm]
    obtain ⟨d,hd,he⟩ := reciprocal_of_unit_constant hu hr
    have h1 : d≠1 := by
      rintro rfl
      have hx : x=1 := by simpa using he
      rw [hx] at hr
      have hz : f.eval (1:ℤ)=0 := by
        have e := eval₂_at_apply (R:=ℤ) (p:=f) (Int.castRingHom ℚ) (1:ℤ)
        have H : (Int.castRingHom ℚ) (f.eval 1)=0 := by
          rw [←e,map_one]
          exact hr
        exact Int.cast_eq_zero.mp H
      dsimp [f] at hz
      rw [polynomialTerm_eval_one] at hz
      cases k <;> simp [hn.ne'] at hz
    have eq := (scaled_root_iff k a n d hd h1).mp (he ▸ h)
    have hm : d≠ -1 := by
      rintro rfl
      rcases Nat.even_or_odd n with h|h
      · rw [h.neg_one_pow] at eq; norm_num at eq; omega
      · rw [h.neg_one_pow] at eq; cases k <;> norm_num [sign] at eq <;> omega
    exact ⟨d,by omega,he,eq⟩
  · rintro ⟨d,hd,rfl,he⟩
    exact (scaled_root_iff k a n d (by omega) (by omega)).mpr he

#print axioms scaled_root_iff
#print axioms rational_root_iff_denominator

end CunninghamChain.LinearRoots
