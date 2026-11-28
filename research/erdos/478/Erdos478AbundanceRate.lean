import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Cost and multiplicity for an exponential count parameter

With `L = 2^(n/d)`, the extra term in the double logarithm of the
prime ceiling is linear in `n/d`, while the number of witnesses
exceeds a double exponential in that same parameter.
-/

namespace Erdos478.EffectiveResolvent
open Real

private theorem half_le_log_two : (1:ℝ)/2 ≤ log 2 := by
  have h := log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ)⁻¹)
  rw [log_inv] at h
  linarith

theorem exclusion_cost {n d : ℕ} {ε : ℝ} (hd : 0<d) (hn : 2*d≤n) (hε : 16 ≤ ε*d) :
    (2*(((n+1)/d:ℕ):ℝ)+2)*log 2 ≤ (ε/4)*(2*n) := by
  have hl : log 2 ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))]
  have hq : (((n+1)/d:ℕ):ℝ)*d ≤ (n:ℝ)+1 := by exact_mod_cast Nat.div_mul_le_self (n+1) d
  have hdr : (d:ℝ) ≤ n := by exact_mod_cast (by omega : d≤n)
  have hnr : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1≤n)
  apply (mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*(((n+1)/d:ℕ):ℝ)+2 by positivity)).trans
  apply le_of_mul_le_mul_right (a := (d:ℝ)) _ (by exact_mod_cast hd)
  have hlim := mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg (α := ℝ) n)
  nlinarith only [hq,hdr,hnr,hlim]

theorem count_exponential {n d : ℕ} (hd : 0<d) (hn : 2*d≤n) :
    exp (exp ((2*(n:ℝ))/(16*d))) ≤ (2:ℝ)^(2^(n/d)) := by
  let q := n/d
  have hq : 2≤q := (Nat.le_div_iff_mul_le hd).mpr hn
  have hqr : (2:ℝ)≤q := by exact_mod_cast hq
  have hnd : (n:ℝ) ≤ 2*(d:ℝ)*q := by
    have hmul : d ≤ d*q := by simpa using Nat.mul_le_mul_left d (show 1≤q by omega)
    have hmod := Nat.mod_lt n hd
    have he : d*q+n%d=n := Nat.div_add_mod n d
    exact_mod_cast (by nlinarith only [hmul,hmod,he] : n≤2*d*q)
  have hc : 2*(n:ℝ)/(16*d) ≤ (q:ℝ)/4 := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hnd])
  have hqlog : (q:ℝ)/4 ≤ (q-1)*log 2 := calc
    _ ≤ ((q:ℝ)-1)*(1/2) := by linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left half_le_log_two (by linarith)
  have hsmall : exp (2*(n:ℝ)/(16*d)) ≤ ((2:ℝ)^q)*log 2 := calc
    _ ≤ exp (((q:ℝ)-1)*log 2) := exp_le_exp.mpr (hc.trans hqlog)
    _ = (2:ℝ)^q/2 := by rw [sub_mul,one_mul,exp_sub,← log_pow,exp_log (by positivity),exp_log (by norm_num)]
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left half_le_log_two (show 0≤(2:ℝ)^q by positivity)]
  calc
    _ ≤ exp (((2^q:ℕ):ℝ)*log 2) := exp_le_exp.mpr (by exact_mod_cast hsmall)
    _ = _ := by rw [← log_pow,exp_log (by positivity)]

#print axioms exclusion_cost
#print axioms count_exponential

end Erdos478.EffectiveResolvent
