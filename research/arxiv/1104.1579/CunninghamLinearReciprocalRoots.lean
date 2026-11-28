import CunninghamPolynomialLengths
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand

/-! Reciprocal root pairs in polynomial Cunningham chains from a linear seed. -/

namespace CunninghamChain.LinearRoots
open Polynomial

def sign (k : Bool) : ℤ := if k then 1 else -1

/-- Jones's nth iterate of the seed aX+b, transferred to rational coefficients. -/
noncomputable def term (k : Bool) (a b : ℤ) (n : ℕ) : ℚ[X] :=
  (polynomialTerm k (C a * X + C b) n).map (Int.castRingHom ℚ)

lemma term_step (k : Bool) (a b : ℤ) (n : ℕ) (z : ℂ) :
    aeval z (term k a b (n+1)) = z * aeval z (term k a b n) + sign k := by
  cases k <;> simp [term,polynomialTerm,sign]

lemma root_equation (k : Bool) (a b : ℤ) (n : ℕ) (z : ℂ) (hz : z ≠ 1) :
    aeval z (term k a b n) = 0 ↔
      z^n * ((z-1)*(a*z+b)+sign k) = sign k := by
  have h : (z-1) * aeval z (term k a b n) =
      z^n * ((z-1)*(a*z+b)+sign k) - sign k := by
    induction n with
    | zero => simp [term,polynomialTerm]
    | succ n ih =>
      rw [term_step,pow_succ]
      linear_combination z*ih
  constructor
  · intro h0
    rw [h0,mul_zero] at h
    linear_combination -h
  · intro h0
    rw [h0,sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hz)

/-- Both a nontrivial root and its inverse can occur only on this reciprocal quadratic. -/
theorem reciprocal_root_equation {k : Bool} {a b : ℤ} {n : ℕ} {z : ℂ}
    (hz : z ≠ 0) (h1 : z ≠ 1) (h : aeval z (term k a b n) = 0)
    (hi : aeval z⁻¹ (term k a b n) = 0) :
    a*(sign k-b)*(z^2+1) + ((a+b)*sign k-a^2-b^2)*z = 0 := by
  let e : ℂ := sign k
  have he : e^2 = 1 := by cases k <;> norm_num [e,sign]
  have hi1 : z⁻¹ ≠ 1 := by simpa using h1
  have hprod := congrArg₂ (· * ·) ((root_equation k a b n z h1).mp h)
    ((root_equation k a b n z⁻¹ hi1).mp hi)
  rw [mul_mul_mul_comm,←mul_pow,mul_inv_cancel₀ hz,one_pow,one_mul] at hprod
  change ((z-1)*(a*z+b)+e)*((z⁻¹-1)*(a*z⁻¹+b)+e) = e*e at hprod
  rw [←pow_two,he] at hprod
  have hs : z^2*((z⁻¹-1)*(a*z⁻¹+b)+e) = (1-z)*(a+b*z)+e*z^2 := by
    field_simp
  have hq : ((z-1)*(a*z+b)+e)*((1-z)*(a+b*z)+e*z^2) = z^2 := by
    rw [←hs, mul_left_comm, hprod, mul_one]
  have hzq : (z-1)^2 * (a*(e-b)*(z^2+1) + ((a+b)*e-a^2-b^2)*z) = 0 := by
    linear_combination hq - z^2*he
  simpa [e] using (mul_eq_zero.mp hzq).resolve_left (pow_ne_zero _ (sub_ne_zero.mpr h1))

lemma primitive_dvd {d : ℕ} (hd : 0 < d) {z : ℂ} (hz : IsPrimitiveRoot z d) (P : ℚ[X]) :
    cyclotomic d ℚ ∣ P ↔ aeval z P = 0 := by
  rw [cyclotomic_eq_minpoly_rat hz hd, minpoly.dvd_iff]

private lemma small_totient {d : ℕ} (hd : 0<d) (hs : d.totient≤2) :
    d=1 ∨ d=2 ∨ d=3 ∨ d=4 ∨ d=6 := by
  have bound {c : ℕ} (hc : c∣d) : c.totient≤2 :=
    (Nat.le_of_dvd (Nat.totient_pos.mpr hd) (Nat.totient_dvd_of_dvd hc)).trans hs
  have div : d∣12 := by
    apply (Nat.dvd_iff_prime_pow_dvd_dvd ..).mpr
    intro p k hp h
    cases k with
    | zero => simp
    | succ k =>
      have hpd : p ∣ d := (dvd_pow_self p (by omega : k+1≠0)).trans h
      have hle := bound hpd
      rw [Nat.totient_prime hp] at hle
      have small := hp.two_le
      rcases (show p=2 ∨ p=3 by omega) with rfl | rfl
      · have hn : k<2 := by
          by_contra! bad
          have hb := bound ((pow_dvd_pow 2 (by omega : 3 ≤ k+1)).trans h)
          exact (by decide : ¬(8:ℕ).totient ≤ 2) hb
        interval_cases k <;> decide
      · have hn : k<1 := by
          by_contra! bad
          have hb := bound ((pow_dvd_pow 3 (by omega : 2 ≤ k+1)).trans h)
          exact (by decide : ¬(9:ℕ).totient ≤ 2) hb
        interval_cases k; decide
  have hle := Nat.le_of_dvd (by decide : 0 < 12) div
  interval_cases d <;> norm_num at *
  exact (by decide : ¬(12:ℕ).totient ≤ 2) hs

/-- Outside the geometric first-kind seed X+1, every cyclotomic factor has order 1,2,3,4 or 6. -/
theorem linear_cyclotomic_orders {k : Bool} {a b : ℤ} (ha : 0<a)
    (hex : ¬ (k=true ∧ a=1 ∧ b=1)) {d n : ℕ} (hd : 0<d)
    (hdiv : cyclotomic d ℚ ∣ term k a b n) : d=1 ∨ d=2 ∨ d=3 ∨ d=4 ∨ d=6 := by
  by_cases h1 : d=1
  · exact Or.inl h1
  let z := Complex.exp (2 * Real.pi * Complex.I / d)
  have hz : IsPrimitiveRoot z d := Complex.isPrimitiveRoot_exp d hd.ne'
  have hr := reciprocal_root_equation (hz.ne_zero hd.ne') (hz.ne_one (by omega))
    ((primitive_dvd hd hz _).mp hdiv) ((primitive_dvd hd hz.inv _).mp hdiv)
  let A : ℤ := a*(sign k-b)
  let B : ℤ := (a+b)*sign k-a^2-b^2
  let Q : ℚ[X] := C (A:ℚ)*X^2+C (B:ℚ)*X+C (A:ℚ)
  have hq : cyclotomic d ℚ ∣ Q := by
    apply (primitive_dvd hd hz _).mpr
    simp [Q,A,B]
    linear_combination hr
  have hne : Q ≠ 0 := by
    intro hh
    have hA := congrArg (fun P : ℚ[X] => P.coeff 0) hh
    have hB := congrArg (fun P : ℚ[X] => P.coeff 1) hh
    simp [Q,coeff_add,coeff_X_pow] at hA hB
    simp [hA] at hB
    have ha0 : a≠0 := by omega
    have heq : b=sign k := by
      have ha' : A=0 := by exact_mod_cast hA
      exact (sub_eq_zero.mp ((mul_eq_zero.mp ha').resolve_left ha0)).symm
    have hb' : B=0 := by exact_mod_cast hB
    subst b
    cases k <;> simp [B,sign] at hb' hex
    · nlinarith [sq_nonneg a]
    · have hlarge : 2 ≤ a := by omega
      nlinarith [mul_nonneg (show 0 ≤ a-2 by omega) ha.le]
  apply small_totient hd
  calc d.totient = (cyclotomic d ℚ).natDegree := (natDegree_cyclotomic ..).symm
       _ ≤ Q.natDegree := natDegree_le_of_dvd hq hne
       _ ≤ 2 := natDegree_quadratic_le

#print axioms reciprocal_root_equation
#print axioms linear_cyclotomic_orders

end CunninghamChain.LinearRoots
