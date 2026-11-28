import HosoyaConjugatePowerNorm
import HosoyaRecurrenceGapNorm

/-! Two terms in one power class at a compatible index gap force a bound on the later term. -/

namespace Arxiv.«2211.10788».PowerGaps
open Real
open scoped goldenRatio

private theorem power_norm {y z h : ℕ} (yp : 0<y) (zp : 0<z) (hp : 0<h) (t : ℕ) :
    (z:ℝ)^(t+2) ≤
      |((z:ℝ)^(t+2)-(φ^(2*h)*y)^(t+2))*(z^(t+2)-(ψ^(2*h)*y)^(t+2))| := by
  let A := φ^(2*h)*y
  let B := ψ^(2*h)*y
  have AP : 0≤A := by dsimp [A];positivity [goldenRatio_pos]
  have BP : 0≤B := by dsimp [B];rw [pow_mul];positivity
  have zz : (1:ℝ)≤z := by exact_mod_cast zp
  have lo : 1≤|((z:ℝ)-A)*(z-B)| := norm_separated (by omega) yp _
  change (z:ℝ)^(t+2) ≤ |(z^(t+2)-A^(t+2))*(z^(t+2)-B^(t+2))|
  calc
    (z:ℝ)^(t+2) ≤ (z:ℝ)^(t+1)*(z:ℝ)^(t+1) := by
      rw [←pow_add];exact pow_le_pow_right₀ zz (by omega)
    _ ≤ ((z:ℝ)^(t+1)*(z:ℝ)^(t+1))*|((z:ℝ)-A)*(z-B)| := le_mul_of_one_le_right (by positivity) lo
    _ = ((z:ℝ)^(t+1)*|z-A|)*((z:ℝ)^(t+1)*|z-B|) := by rw [abs_mul];ring
    _ ≤ _ := by
      rw [abs_mul]
      exact mul_le_mul (power_distance (by positivity) AP (t+1)) (power_distance (by positivity) BP (t+1))
        (mul_nonneg (by positivity) (abs_nonneg _)) (abs_nonneg _)

/-- The multiplier is arbitrary and may be chosen from the two terms.
The exponent is t+2 and the index difference is 2h(t+2). -/
theorem repeated_class_bound (f : ℕ → ℕ) (step : ∀ n, f (n+2)=f (n+1)+f n)
    {d y z n h : ℕ} (dp : 0<d) (yp : 0<y) (zp : 0<z) (hp : 0<h) (t : ℕ)
    (first : f n=d*y^(t+2)) (last : f (n+2*h*(t+2))=d*z^(t+2)) :
    (f (n+2*h*(t+2)):ℝ) ≤ (Nat.fib (2*h*(t+2)):ℝ)^2*
      |(f 1:ℝ)^2 - f 1*f 0 - (f 0:ℝ)^2| := by
  let F (j : ℕ) : ℝ := f j
  have st (j : ℕ) : F (j+2)=F (j+1)+F j := by dsimp only [F]; exact_mod_cast step j
  have norm := gap_norm F st n (2*h*(t+2))
  dsimp only [F] at norm
  rw [←norm,first,last]
  push_cast
  let V := ((z:ℝ)^(t+2)-(φ^(2*h)*y)^(t+2))*((z:ℝ)^(t+2)-(ψ^(2*h)*y)^(t+2))
  have bound : (z:ℝ)^(t+2)≤|V| := power_norm yp zp hp t
  have id : ((d:ℝ)*z^(t+2)-φ^(2*h*(t+2))*(d*y^(t+2)))*
      (d*z^(t+2)-ψ^(2*h*(t+2))*(d*y^(t+2)))=d^2*V := by
    dsimp [V]
    rw [pow_mul φ (2*h),pow_mul ψ (2*h),mul_pow,mul_pow]
    ring
  rw [id,abs_mul,abs_of_nonneg (sq_nonneg _)]
  have d1 : (1:ℝ)≤d := by exact_mod_cast dp
  exact mul_le_mul (by nlinarith [sq_nonneg ((d:ℝ)-1)] : (d:ℝ)≤d^2)
    bound (by positivity) (sq_nonneg _)

#print axioms repeated_class_bound

end Arxiv.«2211.10788».PowerGaps
