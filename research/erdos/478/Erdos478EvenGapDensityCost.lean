import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The cost of saturating the first even factorial gaps

For half-lengths from one through `n`, bound the product of the possible
Galois group orders in terms of the number `n*(n+1)` of forced collisions.
-/

namespace Erdos478.SplittingDensity
open Finset Real

def pairingProduct (R : Finset ℕ) : ℕ := ∏ r∈R, 2^r * r.factorial

theorem double_sum_halves (n : ℕ) : 2 * (∑ r∈Icc 1 n, r) = n*(n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ n+1) (fun r => r)]
    nlinarith

/-- For `D=n*(n+1)`, the logarithm of the product is at most
`D/4 * log (4*D)`. -/
theorem log_pairing_product {n : ℕ} (hn : 0<n) :
    log (pairingProduct (Icc 1 n) : ℝ) ≤
      ((n*(n+1):ℕ):ℝ)/4 * log (4*((n*(n+1):ℕ):ℝ)) := by
  let R := Icc 1 n
  let s := ∑ r∈R, r
  have hsum : 2*s=n*(n+1) := double_sum_halves n
  have hprod : pairingProduct R ≤ (2*n)^s := by
    unfold pairingProduct
    change _ ≤ (2*n)^(∑ r∈R, r)
    rw [← prod_pow_eq_pow_sum]
    apply prod_le_prod'
    intro r hr
    rw [mul_pow]
    exact Nat.mul_le_mul_left _ (r.factorial_le_pow.trans
      (Nat.pow_le_pow_left (mem_Icc.mp hr).2 r))
  have hp : 0<pairingProduct R := Finset.prod_pos (fun _ _ => Nat.mul_pos (by positivity) (Nat.factorial_pos _))
  have he := log_le_log (by exact_mod_cast hp : 0<(pairingProduct R:ℝ)) (by exact_mod_cast hprod :
    (pairingProduct R:ℝ) ≤ ((2*n:ℕ):ℝ)^s)
  rw [Real.log_pow] at he
  have hl := log_le_log (by positivity : 0 < ((2*n:ℕ):ℝ)^2)
    (show ((2*n:ℕ):ℝ)^2 ≤ 4*((n*(n+1):ℕ):ℝ) by push_cast; nlinarith)
  rw [Real.log_pow] at hl
  have hs' : (2:ℝ)*s=((n*(n+1):ℕ):ℝ) := by exact_mod_cast hsum
  change log (pairingProduct R : ℝ) ≤ _
  rw [← hs']
  rw [← hs'] at hl
  push_cast at hl he
  nlinarith [mul_nonneg (show 0≤(s:ℝ) by positivity)
    (sub_nonneg.mpr hl)]

#print axioms double_sum_halves
#print axioms log_pairing_product
end Erdos478.SplittingDensity
