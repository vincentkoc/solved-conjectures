import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# The logarithmic saving from rounding complete even gaps

Round the square root of cT/log T upwards to obtain the number of even
lengths. The logarithm of this square root contributes a negative
log-log term to the cost in the prime ceiling.
-/

namespace Erdos478.EffectiveResolvent
open Real Filter

theorem rounded_complete_gaps {c γ : ℝ} (hc : 0<c) (hγ : γ<c/2) :
    ∀ᶠ T : ℝ in atTop, ∃ n : ℕ, 0<n ∧
      c*T ≤ (n:ℝ)*(n+1)*log T ∧
      ((n:ℝ)*(n+1)+38)*log (2*n+4) ≤
        c/2*T-γ*(T/log T)*log (log T) := by
  let K := log (9*c)+2
  have small := (Real.isLittleO_pow_log_id_atTop (n := 3)).bound (show 0<c/1849 by positivity)
  filter_upwards [small,tendsto_log_atTop.eventually_ge_atTop 1,
    (tendsto_log_atTop.comp tendsto_log_atTop).eventually_ge_atTop
      (max (log (9*c)) ((c/2)*K/(c/2-γ))),eventually_ge_atTop (1:ℝ)] with T hsmall hlog hmax hT
  have hT' : 0<T := by linarith
  have hl : 0<log T := by linarith
  simp only [Function.comp_apply] at hmax
  obtain ⟨hK,hγT⟩ := max_le_iff.mp hmax
  have ha := (div_le_iff₀ (sub_pos.mpr hγ)).mp hγT
  simp only [Real.norm_eq_abs,id_eq,abs_of_pos hT',abs_of_nonneg (pow_nonneg hl.le 3)] at hsmall
  let w := T/log T
  let y := sqrt (c*w)
  have hw : 0<w := div_pos hT' hl
  have hwe : w*log T=T := div_mul_cancel₀ _ hl.ne'
  have hy : 0<y := Real.sqrt_pos.mpr (mul_pos hc hw)
  have hys : y^2=c*w := Real.sq_sqrt (mul_pos hc hw).le
  have hye : y^2*log T=c*T := by rw [hys,mul_assoc,hwe]
  have h43 : 43*log T≤y := by
    have h₁ : (43*log T)^2*log T≤y^2*log T := by rw [hye]; nlinarith only [hsmall]
    have h₂ := (mul_le_mul_iff_left₀ hl).mp h₁
    nlinarith only [h₂,hy,hl,sq_nonneg (y-43*log T)]
  let n := ⌈y⌉₊
  have hn : y≤(n:ℝ) := Nat.le_ceil y
  have hn' : (n:ℝ)≤y+1 := (Nat.ceil_lt_add_one hy.le).le
  have hnpos : 0<n := by exact_mod_cast hy.trans_le hn
  have hlow : y^2≤(n:ℝ)*(n+1) := by
    nlinarith [sq_nonneg ((n:ℝ)-y),mul_nonneg hy.le (sub_nonneg.mpr hn)]
  have hbase : (n:ℝ)*(n+1)+38 ≤ y^2+43*y := by
    nlinarith only [mul_le_mul hn' (by linarith : (n:ℝ)+1≤y+2) (by positivity) (by positivity),h43,hlog]
  let b : ℝ := 2*n+4
  have hb : 0<b := by dsimp [b]; positivity
  have hlb : 0≤log b := log_nonneg (by dsimp [b]; linarith)
  have hlogb := log_le_log hb (by dsimp [b]; linarith : b≤3*y)
  have hidentity : 2*log (3*y)=log (9*c)+log T-log (log T) := by
    have he : (3*y)^2 = (9*c)*T/log T := by rw [mul_pow,hys]; dsimp [w]; ring
    calc
      _ = log ((3*y)^2) := by rw [log_pow]; norm_num
      _ = _ := by rw [he,log_div (by positivity) hl.ne',log_mul (by positivity) hT'.ne']
  have hbl : log b≤log T := by linarith only [hidentity,hK,hlogb,hl]
  have hextra : 43*y*log b≤y^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left (hbl.trans (by linarith only [h43] : log T≤y/43)) hy.le]
  have hcost : ((n:ℝ)*(n+1)+38)*log b ≤ y^2/2*(log T-log (log T)+K) := by
    dsimp [K]
    nlinarith only [mul_le_mul_of_nonneg_right hbase hlb,hextra,
      mul_le_mul_of_nonneg_left (by linarith only [hidentity,hlogb] :
        2*log b ≤ log (9*c)+log T-log (log T)) (sq_nonneg y)]
  refine ⟨n,hnpos,?_,hcost.trans ?_⟩
  · rw [← hye]
    exact mul_le_mul_of_nonneg_right hlow hl.le
  · rw [hys]
    calc
      _ ≤ c/2*(w*log T)-γ*w*log (log T) := by
        nlinarith only [mul_le_mul_of_nonneg_right ha hw.le]
      _ = _ := by rw [hwe]

#print axioms rounded_complete_gaps
end Erdos478.EffectiveResolvent
