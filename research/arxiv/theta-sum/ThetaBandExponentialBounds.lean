import ThetaDenominatorBandScales
import ThetaHighWindowProjection

/-! Uniform centered moments in every active denominator band. -/
namespace Arxiv.«2501.03234».ThetaBandExponentialBounds
open Finset Filter Real ThetaDenominatorBandScales ThetaReciprocalBlocks ThetaTiltBudget ThetaCenteredWindow
open ThetaIdentityModels
open scoped Topology
noncomputable section

theorem ratio {h q : ℕ} (hq : first h ≤ q) (ht : q ≤ scale h) :
    (((2*order h q:ℕ):ℝ)/tilt (expose h q))^(2*order h q) ≤ exp (-saving h) := by
  let k := order h q
  let u := steps h q
  obtain ⟨hu,hk,_,h₁,_,h₂⟩ := ints hq ht
  have HK : 0 < (k:ℝ) := by exact_mod_cast hk
  have HU : (64:ℝ)*((h:ℝ)+1) ≤ u := by exact_mod_cast hu
  have KQ : (scale h:ℝ) ≤ 2*((k:ℝ)*q) := by exact_mod_cast h₂
  have UQ : (q:ℝ) ≤ 2*((u:ℝ)*(1024*((h:ℝ)+1))) := by exact_mod_cast h₁
  have ke : k ≤ scale h := Nat.div_le_self ..
  have h2 : 1/2 ≤ log 2 := by linarith [log_two_gt_d9]
  have h2' : log 2 ≤ 1 := by linarith [log_two_lt_d9]
  have klog : log (2*(k:ℝ)) ≤ ((h:ℝ)+1)*log 2 := by
    have hupp := Real.log_le_log (mul_pos (by norm_num : (0:ℝ)<2) HK) (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr ke : (k:ℝ) ≤ scale h) (by norm_num : (0:ℝ) ≤ 2))
    rw [Real.log_mul (by norm_num) (by dsimp [scale];positivity : (scale h:ℝ)≠0),log_scale] at hupp
    linarith only [hupp]
  let V := tilt (expose h q)
  have hV : 0 < V := by dsimp [V,tilt,expose];positivity
  have hl : log V=log 2*u/4 := by rw [show log V=(1/4:ℝ)*log (expose h q:ℝ) by rw [show V=(expose h q:ℝ)^(1/4:ℝ) by rfl,Real.log_rpow (by dsimp [expose];positivity)],log_expose];dsimp [u];ring
  have hgrad : log (2*(k:ℝ)/V) ≤ -(u:ℝ)/16 := by
    rw [Real.log_div (by positivity) hV.ne',hl]
    nlinarith only [klog,HU,mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α:=ℝ) u),
      mul_le_mul_of_nonneg_left h2' (show 0 ≤ (h:ℝ)+1 by positivity)]
  have hkU : (scale h:ℝ) ≤ 4096*((k:ℝ)*u)*((h:ℝ)+1) := by nlinarith only [KQ,mul_le_mul_of_nonneg_left UQ HK.le]
  have hs : saving h ≤ (k:ℝ)*u/8 := by
    unfold saving;push_cast;rw [div_le_iff₀ (by positivity)];nlinarith only [hkU,mul_nonneg (mul_nonneg HK.le (Nat.cast_nonneg (α:=ℝ) u)) (show 0 ≤ (h:ℝ)+1 by positivity)]
  change (((2*k:ℕ):ℝ)/V)^(2*k) ≤ _
  push_cast
  rw [←Real.exp_log (pow_pos (div_pos (mul_pos (by norm_num) HK) hV) (2*k)),Real.log_pow,Real.exp_le_exp]
  push_cast
  nlinarith only [mul_le_mul_of_nonneg_left hgrad HK.le,hs]

theorem endpoint {h q Y : ℕ} (hq : first h ≤ q) (ht : q ≤ scale h) (hY : Y ≤ ThetaDenominatorBandScales.size q)
    (hz : 12*Z ≤ exp q) :
    (12*Z*(Y:ℝ)^2)^(2*order h q) ≤ exp (18*scale h) := by
  have hZ : 0 ≤ Z := tsum_nonneg fun _ => by positivity
  have hn : (Y:ℝ) ≤ exp (4*(q:ℝ)) := by
    apply (Nat.cast_le.mpr hY).trans
    rw [←Real.log_le_log_iff (by dsimp [ThetaDenominatorBandScales.size];positivity) (exp_pos _),log_size,log_exp]
    nlinarith only [mul_le_mul_of_nonneg_right (show log 2 ≤ 1 by linarith [log_two_lt_d9]) (Nat.cast_nonneg (α:=ℝ) q)]
  have hh := mul_le_mul hz (pow_le_pow_left₀ (Nat.cast_nonneg _) hn 2) (sq_nonneg (Y:ℝ)) (exp_pos _).le
  rw [←Real.exp_nat_mul,←exp_add] at hh
  have H := pow_le_pow_left₀ (mul_nonneg (mul_nonneg (by norm_num) hZ) (sq_nonneg _)) hh (2*order h q)
  apply H.trans
  rw [←exp_nat_mul,exp_le_exp];push_cast
  have b : (order h q:ℝ)*q ≤ scale h := by exact_mod_cast (ints hq ht).2.2.2.2.1
  nlinarith only [b]

theorem moment : ∀ᶠ h : ℕ in atTop,∀ q Y : ℕ,first h ≤ q → q ≤ scale h → Y ≤ ThetaDenominatorBandScales.size q →
    ∀ (W : ThetaSmoothConditionalModel.Window) (X : ℕ),
    (∑ n∈range X,(center Y (expose h q) W n)^(2*order h q)) ≤
      (X:ℝ)*(2*exp total)*exp (-saving h)+2*exp (18*scale h) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp ThetaCenteredMoment.finite
  obtain ⟨J,hJ⟩ := exists_nat_gt (12*Z)
  filter_upwards [eventually_ge_atTop (max T J)] with h hh q Y hq ht hY W X
  have he := (ints hq ht).1
  have H := hT (expose h q) (by
    have hv : steps h q < 2^(steps h q) := Nat.lt_two_pow_self
    change T ≤ 2^(steps h q);omega) Y W X (2*order h q)
  have hz : 12*Z ≤ exp q := by
    have hge := Nat.div_le_self q (1024*(h+1))
    change steps h q ≤ q at hge
    have hj : J ≤ q := by omega
    exact hJ.le.trans ((Nat.cast_le.mpr hj).trans (le_trans (by linarith : (q:ℝ) ≤ (q:ℝ)+1) (Real.add_one_le_exp _)))
  apply H.trans (add_le_add (mul_le_mul_of_nonneg_left (ratio hq ht) (by positivity)) (mul_le_mul_of_nonneg_left (endpoint hq ht hY hz) (by norm_num)))

#print axioms moment
end
end Arxiv.«2501.03234».ThetaBandExponentialBounds
