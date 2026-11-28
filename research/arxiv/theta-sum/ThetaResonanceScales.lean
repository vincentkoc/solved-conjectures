import ThetaResonantBlock

/-! Size of a resonant prefix in the original prime and its own logarithms. -/
namespace Arxiv.«2501.03234».ThetaResonanceScales
open Real Filter Asymptotics
noncomputable section

def depth (p : ℕ) := Nat.log 2 p
def lowerLevel (p : ℕ) := (depth p).sqrt/128

theorem scales : ∀ᶠ p : ℕ in atTop,
    36 ≤ p ∧ 12 ≤ lowerLevel p ∧ 8192*(lowerLevel p)^2 ≤ depth p ∧
      lowerLevel p ≤ depth p ∧ p/2 ≤ 2^(depth p) ∧ 65536*depth p ≤ p/2 ∧
      (depth p:ℝ) ≤ 2*log p ∧ sqrt (log p) ≤ 256*(lowerLevel p:ℝ) := by
  have ht := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hsm := (isLittleO_log_id_atTop.bound (by norm_num : (0:ℝ)<1/262144))
  filter_upwards [ht.eventually_ge_atTop 3000000,(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually hsm,
    eventually_ge_atTop 36] with p hl h hp
  change 3000000 ≤ log (p:ℝ) at hl
  have hp₁ : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have ht₁ := Nat.pow_log_le_self 2 (by omega : p≠0)
  have ht₂ := Nat.lt_pow_succ_log_self (by decide : 1<2) p
  change p<2^(depth p+1) at ht₂
  have haa := log_le_log (show 0<(2:ℝ)^(depth p) by positivity)
    (show (2:ℝ)^(depth p) ≤ p by exact_mod_cast ht₁)
  have hbb := log_le_log hp₁ (show (p:ℝ) ≤ (2:ℝ)^(depth p+1) by exact_mod_cast ht₂.le)
  rw [log_pow] at haa hbb
  push_cast at hbb
  have hda : (depth p:ℝ) ≤ 2*log p := by
    have hb := mul_le_mul_of_nonneg_left (show (1:ℝ)/2 ≤ log 2 by linarith [log_two_gt_d9])
      (Nat.cast_nonneg (depth p))
    linarith
  have hdb : log p ≤ (depth p:ℝ)+1 := by
    have hb := mul_le_mul_of_nonneg_left (show log 2 ≤ 1 by linarith [log_two_lt_d9])
      (show 0 ≤ (depth p:ℝ)+1 by positivity)
    linarith
  have hdeep : 2359296 ≤ depth p := by exact_mod_cast (show (2359296:ℝ) ≤ depth p by linarith)
  have hs₀ : 1536 ≤ (depth p).sqrt := Nat.le_sqrt.mpr hdeep
  have hs : 12 ≤ lowerLevel p := by dsimp [lowerLevel];omega
  have hs' := Nat.div_mul_le_self (depth p).sqrt 128
  change lowerLevel p*128 ≤ (depth p).sqrt at hs'
  have hsq := Nat.sqrt_le' (depth p)
  have hsbound : 8192*(lowerLevel p)^2 ≤ depth p := by
    have hh := Nat.pow_le_pow_left hs' 2
    nlinarith
  have hsl : lowerLevel p ≤ depth p := by nlinarith only [hs,hsbound]
  have hhalf : p/2 ≤ 2^(depth p) := by rw [pow_succ] at ht₂;omega
  have hid : ‖log (p:ℝ)‖ ≤ (1/262144:ℝ)*‖(p:ℝ)‖ := h
  rw [Real.norm_of_nonneg (by linarith),Real.norm_of_nonneg hp₁.le] at hid
  have hfit : 65536*depth p ≤ p/2 := by
    have hz : 131072*depth p ≤ p := by exact_mod_cast (show 131072*(depth p:ℝ) ≤ p by linarith)
    omega
  refine ⟨hp,hs,hsbound,hsl,hhalf,hfit,hda,?_⟩
  have he := Nat.lt_succ_sqrt' (depth p)
  have he' : (depth p:ℝ)+1 ≤ (((depth p).sqrt:ℝ)+1)^2 := by exact_mod_cast he
  have hc : (depth p).sqrt+1 ≤ 256*lowerLevel p := by dsimp [lowerLevel] at hs ⊢;omega
  have hq := sqrt_le_sqrt (hdb.trans he')
  rw [Real.sqrt_sq (by positivity)] at hq
  exact hq.trans (by exact_mod_cast hc)

theorem length_lower {p i N : ℕ} (hs : lowerLevel p ≤ i) (hz : 12 ≤ lowerLevel p)
    (hroot : sqrt (log p) ≤ 256*(lowerLevel p:ℝ)) (hN : 2^i ≤ N) :
    exp (sqrt (log p)/512) ≤ N ∧ 1 ≤ log (log N) ∧ (i:ℝ)+1 ≤ 4*log N := by
  have hp := log_le_log (show 0<(2:ℝ)^i by positivity) (show (2:ℝ)^i ≤ N by exact_mod_cast hN)
  rw [log_pow] at hp
  have hh := mul_le_mul_of_nonneg_left (show (1:ℝ)/2 ≤ log 2 by linarith [log_two_gt_d9])
    (Nat.cast_nonneg i)
  have hi : (12:ℝ) ≤ i := by exact_mod_cast (hz.trans hs)
  have hs' : (lowerLevel p:ℝ) ≤ i := by exact_mod_cast hs
  have hlog : (6:ℝ) ≤ log N := by linarith
  have hN' : 0<(N:ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le (by positivity) hN)
  refine ⟨(le_log_iff_exp_le hN').mp (by linarith),?_,by linarith⟩
  apply (le_log_iff_exp_le (by linarith)).mpr
  linarith [exp_one_lt_three]

theorem strength {i N : ℕ} {E : ℝ} (hN : N ≤ 4*2^i) (hi : (i:ℝ)+1 ≤ 4*log N)
    (hv : 1 ≤ log (log N)) (h : (2:ℝ)^i/(262144*((i:ℝ)+1)*((harmonic (65536*(i+1)):ℝ)+2))<E) :
    (N:ℝ)/(134217728*log N*log (log N))<E := by
  have hi₀ : 0<(i:ℝ)+1 := by positivity
  have hu : 0<log (N:ℝ) := by linarith
  have hv₀ : 0<log (log (N:ℝ)) := by linarith
  have hH : (0:ℝ)<harmonic (65536*(i+1)) := by exact_mod_cast harmonic_pos (by omega : 65536*(i+1)≠0)
  have hlog : log ((65536*(i+1):ℕ):ℝ) ≤ 18+log (log N) := by
    apply (log_le_log (by positivity) (show ((65536*(i+1):ℕ):ℝ) ≤ (2:ℝ)^18*log N by push_cast;norm_num;nlinarith)).trans
    rw [log_mul (by positivity) hu.ne',log_pow]
    push_cast
    linarith [log_two_lt_d9]
  have hhar : (harmonic (65536*(i+1)):ℝ)+2 ≤ 32*log (log N) := by
    linarith [harmonic_le_one_add_log (65536*(i+1))]
  have hn : (N:ℝ) ≤ 4*(2:ℝ)^i := by exact_mod_cast hN
  apply lt_of_le_of_lt _ h
  have hh : 0 < (harmonic (65536*(i+1)):ℝ)+2 := by linarith only [hH]
  apply (div_le_div_iff₀ (mul_pos (mul_pos (by norm_num) hu) hv₀)
    (mul_pos (mul_pos (by norm_num) hi₀) hh)).mpr
  calc
    _ ≤ (4*(2:ℝ)^i)*(262144*(4*log N)*(32*log (log N))) := by
      apply mul_le_mul hn _ (mul_nonneg (mul_nonneg (by norm_num) hi₀.le) hh.le) (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hi (by norm_num)) hhar hh.le (by positivity)
    _ = _ := by ring

#print axioms scales
#print axioms length_lower
#print axioms strength
end
end Arxiv.«2501.03234».ThetaResonanceScales
