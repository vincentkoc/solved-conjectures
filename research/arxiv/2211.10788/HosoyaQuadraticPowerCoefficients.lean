import LucasFibonacciProgressionDivisors

/-! Integer coordinates in the Fibonacci quadratic algebra under powers and scalar reduction. -/

namespace Arxiv.«2211.10788».IndexDivisors

abbrev Q := QuadraticAlgebra ℕ 1 1
abbrev w : Q := QuadraticAlgebra.omega
abbrev start : Q := ⟨3,1⟩

private lemma coeff_step (z : Q) (n : ℕ) :
    (z*w^(n+2)).im = (z*w^(n+1)).im+(z*w^n).im := by
  have hw : w^2=w+1 := by rw [pow_two,QuadraticAlgebra.omega_mul_omega_eq_add]; simp [add_comm]
  rw [pow_add,hw,mul_add,mul_one,mul_add,pow_succ,←mul_assoc]
  rfl

lemma upper_coeff (n : ℕ) : (start*w^n).im=lucasFibonacciSum n := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h₀ h₁ => rw [coeff_step,lucas_fibonacci_sum_recurrence,h₀,h₁]

lemma fib_coord (n : ℕ) : (w^n).im=Nat.fib n := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h₀ h₁ => simpa [h₀,h₁,Nat.fib_add_two,add_comm] using coeff_step 1 n

lemma primitive_shift (z : Q) (hz : z.re.Coprime z.im) (n : ℕ) :
    (z*w^n).re.Coprime (z*w^n).im := by
  induction n with
  | zero => simpa
  | succ n ih =>
    rw [pow_succ,←mul_assoc,mul_comm (z*w^n) w]
    generalize z*w^n = u at ih ⊢
    obtain ⟨a,b⟩ := u
    simpa [QuadraticAlgebra.omega_mul_mk,Nat.Coprime, Nat.gcd_comm] using ih

private def geom (z : Q) : ℕ → ℕ
  | 0 => 0
  | n+1 => (z^n).re + (z.re+z.im)*geom z n

private lemma power_im (z : Q) (r : ℕ) : (z^r).im=z.im*geom z r := by
  induction r with
  | zero => simp [geom,QuadraticAlgebra.im_one]
  | succ n ih => rw [pow_succ,QuadraticAlgebra.im_mul,ih,geom]; ring

lemma im_dvd_power (z : Q) (r : ℕ) : z.im ∣ (z^r).im := by
  rw [power_im]
  exact dvd_mul_right ..

private lemma power_re_mod (z : Q) {p : ℕ} (h : p ∣ z.im) (r : ℕ) :
    ((z^r).re : ZMod p) = (z.re : ZMod p)^r := by
  have hz := (ZMod.natCast_eq_zero_iff ..).mpr h
  induction r with
  | zero => simp [QuadraticAlgebra.re_one]
  | succ n ih => simp [pow_succ,QuadraticAlgebra.re_mul,hz,ih]

private lemma geom_mod (z : Q) {p : ℕ} (h : p ∣ z.im) (r : ℕ) :
    (geom z (r+1) : ZMod p) = (r+1:ℕ)*(z.re : ZMod p)^r := by
  have hz := (ZMod.natCast_eq_zero_iff ..).mpr h
  induction r with
  | zero => simp [geom,QuadraticAlgebra.re_one]
  | succ n ih =>
    rw [geom]
    push_cast
    rw [power_re_mod z h,ih,hz,pow_succ]
    push_cast
    ring

/-- Raising an element whose imaginary coordinate vanishes modulo p to a tame
power preserves all p-power divisibility of that coordinate when the real part is a unit. -/
theorem tame_power {p : ℕ} (hp : p.Prime) (z : Q) (hz : p ∣ z.im)
    (hu : ¬p ∣ z.re) {r : ℕ} (hr : ¬p ∣ r) (e : ℕ) :
    p^e ∣ (z^r).im ↔ p^e ∣ z.im := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show r≠0 from fun h => hr (h ▸ dvd_zero p))
  have hq : ¬p ∣ geom z (j+1) := by
    rw [←ZMod.natCast_eq_zero_iff,geom_mod z hz]
    exact mul_ne_zero ((ZMod.natCast_eq_zero_iff ..).not.mpr hr)
      (pow_ne_zero _ ((ZMod.natCast_eq_zero_iff ..).not.mpr hu))
  rw [power_im]
  exact ((hp.coprime_iff_not_dvd.mpr hq).pow_left e).dvd_mul_right

/-- Each wild powering gains at least one p-adic digit in the imaginary coordinate. -/
theorem wild_power {p : ℕ} (hp : p.Prime) (z : Q) (hz : p ∣ z.im) (e : ℕ) :
    p^(e+1) ∣ (z^(p^e)).im := by
  induction e with
  | zero => simpa
  | succ e ih =>
    let u := z^(p^e)
    have hpu : p ∣ u.im := (dvd_pow_self p (by omega : e+1≠0)).trans ih
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
    have hq : p ∣ geom u p := by
      apply (ZMod.natCast_eq_zero_iff ..).mp
      have h := geom_mod u hpu j
      rw [show j+1=p by omega] at h
      rw [h,ZMod.natCast_self,zero_mul]
    rw [pow_succ p e,pow_mul,power_im, pow_succ p (e+1)]
    exact Nat.mul_dvd_mul ih hq

lemma scalar_product {m : ℕ} (z u : Q) (h : m ∣ u.im) (hu : m.Coprime u.re) :
    m ∣ (z*u).im ↔ m ∣ z.im := by
  rw [QuadraticAlgebra.im_mul]
  have he : z.re*u.im+z.im*u.re+1*z.im*u.im = z.im*u.re+(z.re+z.im)*u.im := by ring
  rw [he, ←hu.dvd_mul_right (m:=z.im)]
  exact (Nat.dvd_add_iff_left (dvd_mul_of_dvd_right h _)).symm

#print axioms tame_power
#print axioms wild_power

end Arxiv.«2211.10788».IndexDivisors
