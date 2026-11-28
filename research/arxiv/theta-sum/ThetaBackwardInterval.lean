import ThetaBHPIntervals

/-! Backward intervals at the exponent 13/25 in the ordinary-prime progression estimate. -/
namespace Arxiv.«2501.03234».ThetaBackwardInterval
open Finset Filter Real ThetaShortPrimeInterval ThetaStrongDeviation ThetaStrongOriginalTail
noncomputable section

def width (x : ℕ) : ℝ := (x:ℝ)^(13/25:ℝ)
def left (x : ℕ) : ℕ := ⌊(x:ℝ)-width x⌋₊
def length (x : ℕ) : ℕ := x-left x
def window (x : ℕ) (P : ℕ → Prop) := primes (left x) (length x) P

private theorem width_le {x : ℕ} (hx : 1≤x) : width x≤x := by
  exact (rpow_le_rpow_of_exponent_le (by exact_mod_cast hx) (by norm_num : (13/25:ℝ)≤1)).trans_eq (rpow_one _)

theorem mem_window {x p : ℕ} (hx : 1≤x) {P : ℕ → Prop} : p∈window x P ↔
    (x:ℝ)-width x<p ∧ p≤x ∧ p.Prime ∧ P p := by
  have h := width_le hx
  have hn : left x≤x := (Nat.floor_le_of_le (by linarith only [show 0≤width x by unfold width; positivity]))
  rw [window,mem_primes,mem_Ioc,length,Nat.add_sub_of_le hn]
  simp only [left,Nat.floor_lt (sub_nonneg.mpr h),and_assoc]

private theorem endpoints : ∀ᶠ x : ℕ in atTop,
    2≤left x ∧ left x≤x ∧ x≤2*left x ∧ length x≤left x ∧
    width x≤(length x:ℝ) ∧ (length x:ℝ)≤2*width x := by
  have hg := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<12/25)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hg.eventually_ge_atTop 4,eventually_ge_atTop 8] with x h4 hx
  change 4≤(x:ℝ)^(12/25:ℝ) at h4
  have h1 : 1≤(x:ℝ) := by exact_mod_cast (show 1≤x by omega)
  have hp : 0<(x:ℝ) := by linarith
  have hu : 1≤width x := one_le_rpow h1 (by norm_num)
  have hw : 4*width x≤(x:ℝ) := by
    apply (mul_le_mul_of_nonneg_right h4 (by positivity : 0≤(x:ℝ)^(13/25:ℝ))).trans_eq
    rw [←rpow_add hp,show (12/25:ℝ)+13/25=1 by norm_num,rpow_one]
  have hfloor := Nat.floor_le (by linarith : 0≤(x:ℝ)-width x)
  have hf := Nat.lt_floor_add_one ((x:ℝ)-width x)
  change (left x:ℝ)≤_ at hfloor
  change _<(left x:ℝ)+1 at hf
  have hleft : left x≤x := by exact_mod_cast (by linarith : (left x:ℝ)≤x)
  have hhalf : x≤2*left x := by exact_mod_cast (by linarith : (x:ℝ)≤2*(left x:ℝ))
  refine ⟨by omega,hleft,hhalf,by dsimp [length];omega,?_,?_⟩ <;>
    rw [length,Nat.cast_sub hleft] <;> linarith

theorem tendsto_left : Tendsto left atTop atTop := by
  apply tendsto_atTop.mpr
  intro n
  filter_upwards [endpoints,eventually_ge_atTop (2*n)] with x h hx
  omega

theorem admissible : ∀ᶠ x : ℕ in atTop,
    sqrt (left x)*exp (rate (left x)/512)≤length x ∧ length x≤left x ∧
    (length x:ℝ)≤2*width x ∧ log x≤2*log (left x) ∧ 1≤log (left x) := by
  have hl := (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).comp tendsto_left
  filter_upwards [endpoints,hl.eventually_ge_atTop 1] with x ⟨hb,hbx,hxb,hlen,hlo,hhi⟩ hlog
  change 1≤log (left x:ℝ) at hlog
  have h1 : 1≤(left x:ℝ) := by exact_mod_cast (show 1≤left x by omega)
  have hx : 1≤(x:ℝ) := h1.trans (by exact_mod_cast hbx)
  have hp : 0<(left x:ℝ) := by linarith
  have he : exp (rate (left x)/512)≤(left x:ℝ)^(1/512:ℝ) := by
    rw [rpow_def_of_pos hp]
    apply exp_le_exp.mpr
    linarith only [rate_le hlog]
  refine ⟨?_,hlen,hhi,?_,hlog⟩
  · rw [sqrt_eq_rpow]
    apply (mul_le_mul_of_nonneg_left he (by positivity)).trans
    rw [←rpow_add hp]
    apply le_trans _ hlo
    exact (rpow_le_rpow (by positivity) (by exact_mod_cast hbx) (by norm_num)).trans
      (rpow_le_rpow_of_exponent_le hx (by norm_num : (1/2:ℝ)+1/512≤13/25))
  · have h2 : 2≤(left x:ℝ) := by exact_mod_cast hb
    have hz : (x:ℝ)≤(left x:ℝ)^2 := by
      have H : (x:ℝ)≤2*(left x:ℝ) := by exact_mod_cast hxb
      nlinarith only [H,mul_le_mul_of_nonneg_right h2 hp.le]
    simpa only [Real.log_pow,Nat.cast_ofNat] using log_le_log (by linarith : 0<(x:ℝ)) hz

#print axioms mem_window
#print axioms tendsto_left
#print axioms admissible
end
end Arxiv.«2501.03234».ThetaBackwardInterval
