import ThetaShortCenteredInterval
import ThetaShortProgressions

/-! The centered bound at the 13/25 backward interval scale. -/
namespace Arxiv.«2501.03234».ThetaCenteredBackward
open Real Filter Finset ThetaCenteredDeviation ThetaBackwardInterval ThetaShortProgressions
noncomputable section

theorem count (weil : ThetaWeilShortIntervals.Weil) {ε : ℝ} (hε : 0<ε) :
    ∃ b : ℝ, 0<b ∧ b≤1/1024 ∧ ∀ᶠ x : ℕ in atTop,
    ((window x (deviates ε)).card:ℝ) ≤ width x*exp (-b*rate (left x)) := by
  obtain ⟨a,C,ha,hC,h⟩ := ThetaShortCenteredInterval.square_root weil hε
  let b := min (a/2) (1/1024:ℝ)
  have hb : 0<b := lt_min (by positivity) (by norm_num)
  have hb1 : b≤1/1024 := min_le_right ..
  have hba : b≤a/2 := min_le_left ..
  refine ⟨b,hb,hb1,?_⟩
  filter_upwards [tendsto_left.eventually h,tendsto_left.eventually_ge_atTop 2,admissible,
    tendsto_left.eventually (ThetaShortCenteredInterval.absorb hC hb 8),
    tendsto_left.eventually (ThetaShortCenteredInterval.absorb (by norm_num : (0:ℝ)<3) hb 0)] with x hX h2 hw hpoly hthree
  obtain ⟨_,hle',hhi,_,hL⟩ := hw
  have hle : left x≤x := Nat.floor_le_of_le (by linarith only [show 0≤width x by unfold width;positivity])
  let Y := left x
  let R := rate (Y:ℝ)
  have hRp : 0<R := rate_pos _
  have hL' : 0<log (Y:ℝ) := by change 1≤log (Y:ℝ) at hL;linarith
  have hY : 0<(Y:ℝ) := by exact_mod_cast (show 0<left x by omega)
  have hY1 : (1:ℝ)≤Y := by exact_mod_cast (show 1≤left x by omega)
  have hX1 : (1:ℝ)≤x := hY1.trans (by exact_mod_cast hle)
  have hfreq : exp (3*b*R)≤(Y:ℝ)^(1/128:ℝ) := by
    rw [rpow_def_of_pos hY,exp_le_exp]
    change 1≤log (Y:ℝ) at hL
    nlinarith only [mul_le_mul_of_nonneg_right hb1 hRp.le,rate_le hL,hL]
  have hmass : sqrt (Y:ℝ)*exp (3*b*R)≤width x := by
    rw [sqrt_eq_rpow]
    apply (mul_le_mul_of_nonneg_left hfreq (by positivity)).trans
    rw [←rpow_add hY]
    change _≤(x:ℝ)^(13/25:ℝ)
    exact (rpow_le_rpow hY.le (by exact_mod_cast hle) (by norm_num)).trans
      (rpow_le_rpow_of_exponent_le hX1 (by norm_num))
  have hoff : C*sqrt (Y:ℝ)*(1+log Y)^8 ≤ width x*exp (-2*b*R) := by
    change C*(1+log Y)^8≤exp (b*R) at hpoly
    have h₁ := mul_le_mul_of_nonneg_left hpoly (sqrt_nonneg (Y:ℝ))
    have h₂ := mul_le_mul_of_nonneg_right hmass (exp_pos (-2*b*R)).le
    rw [mul_assoc,←exp_add,show 3*b*R+ -2*b*R=b*R by ring] at h₂
    linarith only [h₁,h₂]
  have hh := hX (length x) hle'
  rw [←rate_eq hL'] at hh
  have hfirst : (length x:ℝ)/log Y*exp (-a*R)≤2*width x*exp (-2*b*R) :=
    mul_le_mul ((div_le_self (Nat.cast_nonneg _) hL).trans hhi)
      (exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_right hba hRp.le]))
      (exp_pos _).le (by dsimp [width]; positivity)
  change ((window x (deviates ε)).card:ℝ)≤(length x:ℝ)/log Y*exp (-a*R)+C*sqrt (Y:ℝ)*(1+log Y)^8 at hh
  simp only [pow_zero,mul_one] at hthree
  change 3≤exp (b*R) at hthree
  have hfin : 3*exp (-2*b*R)≤exp (-b*R) := by
    apply (mul_le_mul_of_nonneg_right hthree (exp_pos (-2*b*R)).le).trans_eq
    rw [←exp_add];congr 1;ring
  have hw0 : 0≤width x := by dsimp [width]; positivity
  nlinarith only [hh,hoff,hfirst,mul_le_mul_of_nonneg_left hfin hw0]

#print axioms count
end
end Arxiv.«2501.03234».ThetaCenteredBackward
