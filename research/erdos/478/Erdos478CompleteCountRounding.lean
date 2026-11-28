import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Exponential witness counts within a prime cutoff

A count parameter slightly above twice exp(αT) gives at least
exp(exp(αT)) witnesses. Its logarithmic cost is at most αT+log 4.
-/

namespace Erdos478.EffectiveResolvent
open Real

theorem rounded_witness_count {a : ℝ} (ha : 0≤a) :
    ∃ L : ℕ, exp (exp a) ≤ (2:ℝ)^L ∧ log ((L:ℝ)+1)≤a+log 4 := by
  let L := ⌈2*exp a⌉₊
  have hlo : 2*exp a≤(L:ℝ) := Nat.le_ceil _
  have hhi : (L:ℝ)≤2*exp a+1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hlog : (1:ℝ)/2≤log 2 := by
    have h := log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ)⁻¹)
    rw [log_inv] at h
    linarith
  have h1 : 1≤exp a := Real.one_le_exp ha
  refine ⟨L,?_,?_⟩
  · calc
      _ ≤ exp ((L:ℝ)*log 2) := exp_le_exp.mpr (by
        nlinarith only [hlo,mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) L)])
      _ = _ := by rw [← log_pow,exp_log (by positivity)]
  · calc
      _ ≤ log (exp a*4) := log_le_log (by positivity) (by linarith)
      _ = _ := by rw [log_mul (exp_pos _).ne' (by norm_num),log_exp]

/-- A logarithmic budget for the base-two ceiling transfers to the
original natural cutoff. -/
theorem nat_ceiling_within {b d L X : ℕ} (hb : 0<b) (hX : 1<X)
    (h : (d:ℝ)*log b+2*log ((L:ℝ)+1)≤log (log X)) :
    2^(b^d*(L+1)^2)≤X := by
  let E := b^d*(L+1)^2
  have hE : (0:ℝ)<E := by dsimp [E]; positivity
  have hx : (0:ℝ)<log X := log_pos (by exact_mod_cast hX)
  have hlog : log (E:ℝ)≤log (log X) := by
    dsimp [E]
    push_cast
    rwa [log_mul (by positivity) (by positivity),log_pow,log_pow]
  have h₁ : (E:ℝ)≤log X := (log_le_log_iff hE hx).mp hlog
  have h₂ := log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))
  have he : log ((2:ℝ)^E)≤log X := by
    rw [log_pow]
    nlinarith only [h₁,mul_le_mul_of_nonneg_left h₂ hE.le]
  have out := (log_le_log_iff (by positivity) (by exact_mod_cast (show 0<X by omega))).mp he
  exact_mod_cast out

#print axioms rounded_witness_count
#print axioms nat_ceiling_within
end Erdos478.EffectiveResolvent
