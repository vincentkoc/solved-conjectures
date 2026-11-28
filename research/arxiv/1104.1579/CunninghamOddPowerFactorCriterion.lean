import Mathlib

/-! A three-coefficient criterion forcing a unit constant in any integral factorization. -/

namespace CunninghamChain
open Polynomial Finset

lemma coeff_two_product (A B : ℤ[X]) :
    (A*B).coeff 2 = A.coeff 0*B.coeff 2 + (A.coeff 1*B.coeff 1 + A.coeff 2*B.coeff 0) := by
  rw [coeff_mul,Nat.antidiagonal_eq_map]
  simp [Finset.sum_range_succ,add_assoc]
  rfl

/-- A divisor of a prime power is coprime to any integer prime to the base. -/
private lemma abs_divisor_coprime {p e : ℕ} (hp : p.Prime) {a b : ℤ}
    (hd : a.natAbs ∣ p^e) (hn : ¬(p:ℤ) ∣ b) : a.natAbs.Coprime b.natAbs := by
  obtain ⟨i,_,he⟩ := (Nat.dvd_prime_pow hp).mp hd
  rw [he]
  apply Nat.Coprime.pow_left
  apply hp.coprime_iff_not_dvd.mpr
  intro h
  apply hn
  exact Int.natAbs_dvd_natAbs.mp (by simpa using h)

private lemma prime_dvd_nonunit {p e : ℕ} (hp : p.Prime) {a : ℤ}
    (hd : a.natAbs ∣ p^e) (hna : ¬IsUnit a) : (p:ℤ) ∣ a := by
  obtain ⟨i,_,he⟩ := (Nat.dvd_prime_pow hp).mp hd
  cases i with
  | zero => exact (hna (Int.isUnit_iff_natAbs_eq.mpr (by simpa using he))).elim
  | succ i =>
    apply Int.natAbs_dvd_natAbs.mp
    simp [he,pow_succ]

/-- If neither constant is a unit, cancellation in the linear coefficient forces their
absolute values to agree, for any exponent of the prime. -/
theorem factor_constants_natAbs_eq {p e : ℕ} (hp : p.Prime) (A B : ℤ[X])
    (h₀ : ((A*B).coeff 0).natAbs = p^e)
    (h₁ : (A*B).coeff 0 ∣ (A*B).coeff 1) (h₂ : ¬(p:ℤ) ∣ (A*B).coeff 2)
    (ha : ¬IsUnit (A.coeff 0)) (hb : ¬IsUnit (B.coeff 0)) :
    (A.coeff 0).natAbs = (B.coeff 0).natAbs := by
  rw [mul_coeff_zero,Int.natAbs_mul] at h₀
  rw [mul_coeff_zero,mul_coeff_one] at h₁
  rw [coeff_two_product] at h₂
  have da : (A.coeff 0).natAbs ∣ p^e := h₀ ▸ dvd_mul_right _ _
  have db : (B.coeff 0).natAbs ∣ p^e := h₀ ▸ dvd_mul_left _ _
  have pa := prime_dvd_nonunit hp da ha
  have pb := prime_dvd_nonunit hp db hb
  have mid : ¬(p:ℤ) ∣ A.coeff 1*B.coeff 1 := fun hm => h₂
    (dvd_add (dvd_mul_of_dvd_left pa _) (dvd_add hm (dvd_mul_of_dvd_right pb _)))
  have ca := abs_divisor_coprime hp da (fun h => mid (dvd_mul_of_dvd_left h _))
  have cb := abs_divisor_coprime hp db (fun h => mid (dvd_mul_of_dvd_right h _))
  have ab : A.coeff 0 ∣ A.coeff 1*B.coeff 0 :=
    (dvd_add_right (dvd_mul_right ..)).mp ((dvd_mul_right ..).trans h₁)
  have ba : B.coeff 0 ∣ A.coeff 0*B.coeff 1 :=
    (dvd_add_left (dvd_mul_left ..)).mp ((dvd_mul_left ..).trans h₁)
  have ab' := Int.natAbs_dvd_natAbs.mpr ab
  have ba' := Int.natAbs_dvd_natAbs.mpr ba
  rw [Int.natAbs_mul] at ab' ba'
  exact Nat.dvd_antisymm (ca.dvd_of_dvd_mul_left ab') (cb.dvd_of_dvd_mul_right ba')

/-- If the constant has absolute value an odd power of p, divides the linear coefficient,
and the quadratic coefficient survives modulo p, then one factor has unit constant. -/
theorem unit_constant_of_odd_power {p r : ℕ} (hp : p.Prime) (A B : ℤ[X])
    (h₀ : ((A*B).coeff 0).natAbs = p^(2*r+1))
    (h₁ : (A*B).coeff 0 ∣ (A*B).coeff 1) (h₂ : ¬(p:ℤ) ∣ (A*B).coeff 2) :
    IsUnit (A.coeff 0) ∨ IsUnit (B.coeff 0) := by
  by_contra! h
  have eq := factor_constants_natAbs_eq hp A B h₀ h₁ h₂ h.1 h.2
  rw [mul_coeff_zero,Int.natAbs_mul] at h₀
  have da : (A.coeff 0).natAbs ∣ p^(2*r+1) := h₀ ▸ dvd_mul_right _ _
  obtain ⟨i,_,hi⟩ := (Nat.dvd_prime_pow hp).mp da
  rw [←eq,hi,←pow_add] at h₀
  have := Nat.pow_right_injective hp.two_le h₀
  omega

/-- At even positive exponents the three-coefficient condition alone permits two nonunit
constants. The factors q + X and q − X give q² − X². -/
theorem even_power_counterexample {p r : ℕ} (hp : p.Prime) (hr : 0<r) :
    ∃ A B : ℤ[X], ((A*B).coeff 0).natAbs = p^(2*r) ∧
      (A*B).coeff 0 ∣ (A*B).coeff 1 ∧ ¬(p:ℤ) ∣ (A*B).coeff 2 ∧
      ¬IsUnit (A.coeff 0) ∧ ¬IsUnit (B.coeff 0) := by
  let q : ℤ := (p^r:ℕ)
  have hq : ¬IsUnit q := by
    rw [Int.isUnit_iff_natAbs_eq]
    simpa [q] using (one_lt_pow₀ hp.one_lt hr.ne').ne'
  have hpn : ¬(p:ℤ) ∣ -1 := by simpa using (Nat.prime_iff_prime_int.mp hp).not_dvd_one
  refine ⟨C q+X,C q-X,?_,?_,?_,?_,?_⟩
  · simp only [mul_coeff_zero,coeff_add,coeff_sub,coeff_C,coeff_X]
    norm_num [q,Int.natAbs_mul,two_mul,pow_add]
  · simp only [mul_coeff_zero,mul_coeff_one,coeff_add,coeff_sub,coeff_C,coeff_X]
    norm_num
  · simp only [coeff_two_product,coeff_add,coeff_sub,coeff_C,coeff_X]
    simpa using hpn
  · simpa using hq
  · simpa using hq

#print axioms factor_constants_natAbs_eq
#print axioms unit_constant_of_odd_power
#print axioms even_power_counterexample

end CunninghamChain
