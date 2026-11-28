import Mathlib

/-! Integral norms bound repeated occurrences of a power class in a Fibonacci recurrence. -/
namespace Arxiv.«2211.10788».PowerGaps
open Real
open scoped goldenRatio

private theorem no_root {α β : ℝ} (irr : Irrational β) {h y z : ℕ}
    (fh : 0<Nat.fib h) (yp : 0<y)
    (repr : (Nat.fib (h+1):ℝ)-β*Nat.fib h=α^h) : (z:ℝ)-α^h*y ≠ 0 := by
  intro eq
  apply irr.ne_rat (((Nat.fib (h+1):ℚ)*y-z)/(Nat.fib h*y))
  push_cast
  apply (eq_div_iff (by positivity)).mpr
  rw [←repr] at eq
  linarith only [show β*(Nat.fib h*y)=(β*Nat.fib h)*y by ring,
    show (Nat.fib (h+1):ℝ)*y-β*Nat.fib h*y=(Nat.fib (h+1)-β*Nat.fib h)*y by ring,eq]

/-- The two conjugate differences have nonzero integral product. -/
theorem norm_separated {h y : ℕ} (hp : 0<h) (yp : 0<y) (z : ℕ) :
    1 ≤ |((z:ℝ)-φ^h*y)*(z-ψ^h*y)| := by
  let L : ℤ := 2*(Nat.fib (h+1):ℤ)-Nat.fib h
  let t : ℤ := (z:ℤ)^2-L*y*z+(-1)^h*(y:ℤ)^2
  have tr : φ^h+ψ^h=(L:ℝ) := by
    dsimp [L];push_cast
    rw [←fib_succ_sub_goldenConj_mul_fib,←fib_succ_sub_goldenRatio_mul_fib]
    nlinarith only [congrArg (fun u : ℝ => u*Nat.fib h) goldenRatio_add_goldenConj]
  have prod : φ^h*ψ^h=(-1:ℝ)^h := by rw [←mul_pow,goldenRatio_mul_goldenConj]
  have norm : ((z:ℝ)-φ^h*y)*(z-ψ^h*y)=(t:ℝ) := by
    change _ = (((z:ℤ)^2-L*y*z+(-1)^h*(y:ℤ)^2:ℤ):ℝ)
    push_cast
    rw [←tr,←prod]
    ring
  have nz : t≠0 := by
    intro empty
    have zero : ((z:ℝ)-φ^h*y)*(z-ψ^h*y)=0 := by rw [norm,empty];norm_num
    exact (mul_ne_zero (no_root goldenConj_irrational (Nat.fib_pos.mpr hp) yp
      (fib_succ_sub_goldenConj_mul_fib h)) (no_root goldenRatio_irrational (Nat.fib_pos.mpr hp) yp
      (fib_succ_sub_goldenRatio_mul_fib h))) zero
  rw [norm]
  exact_mod_cast Int.one_le_abs nz

/-- Taking powers cannot shrink the difference below the leading-power contribution. -/
theorem power_distance {x a : ℝ} (xp : 0≤x) (ap : 0≤a) (j : ℕ) :
    x^j*|x-a| ≤ |x^(j+1)-a^(j+1)| := by
  rcases le_total a x with le|le
  · rw [abs_of_nonneg (sub_nonneg.mpr le),abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ ap le _))]
    have bound := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ap le j) ap
    rw [pow_succ,pow_succ,mul_sub]
    linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr le),abs_of_nonpos (sub_nonpos.mpr (pow_le_pow_left₀ xp le _))]
    have bound := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ xp le j) ap
    rw [pow_succ,pow_succ]
    nlinarith only [bound]

#print axioms norm_separated
#print axioms power_distance
end Arxiv.«2211.10788».PowerGaps
