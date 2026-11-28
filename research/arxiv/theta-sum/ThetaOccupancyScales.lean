import ThetaMultiscaleExceptions

/-! Endpoint estimates for simultaneous exceptional-prime counts across moduli. -/
namespace Arxiv.«2501.03234».ThetaOccupancyScales
open Filter Real
noncomputable section

def saving (X : ℕ) := log (X:ℝ)/(1+log (log X))/268435456

theorem bounds : ∀ᶠ X : ℕ in atTop,0<(X:ℝ) ∧ 1≤log (X:ℝ) ∧ 1≤ saving X ∧ saving X≤log X ∧
    (1+log (X:ℝ))^3 ≤ exp (saving X) ∧ (X:ℝ) ≤ X.primeCounting*exp (saving X) := by
  have hn := tendsto_natCast_atTop_atTop (R:=ℝ)
  have hl := tendsto_log_atTop.comp hn
  have hh := hl.eventually ((isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ)<1)).bound
    (by norm_num : (0:ℝ)<1/34359738368))
  filter_upwards [hh,(tendsto_log_atTop.comp hl).eventually_ge_atTop 1,hl.eventually_ge_atTop 1,
    hn.eventually_gt_atTop 0,ThetaPrimeDensity.prime_count_lower] with X hsmall hll hlog hx hπ
  let L := log (X:ℝ)
  let u := log L
  change 1≤u at hll
  change 1≤L at hlog
  have hL : 0<L := by linarith
  have hu : 0≤u := by linarith
  change ‖u^(2:ℝ)‖ ≤ (1/34359738368)*‖L^(1:ℝ)‖ at hsmall
  rw [rpow_two,rpow_one,Real.norm_of_nonneg (sq_nonneg _),Real.norm_of_nonneg hL.le] at hsmall
  have hs : 16*u ≤ saving X := by
    change _ ≤ L/(1+u)/268435456
    rw [le_div_iff₀ (by norm_num),le_div_iff₀ (by linarith)]
    nlinarith only [hsmall,mul_le_mul_of_nonneg_left hll hu]
  have hupper : saving X≤L := by
    change L/(1+u)/268435456≤L
    have h₁ := div_le_self hL.le (show 1≤1+u by linarith)
    exact (div_le_self (div_nonneg hL.le (by linarith)) (by norm_num : (1:ℝ)≤268435456)).trans h₁
  have h4 : 4*L ≤ exp (saving X) := by
    rw [←exp_log (by norm_num : 0<(4:ℝ)),←exp_log hL,←exp_add,exp_le_exp]
    have h := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
    change log 4+u ≤ _
    linarith only [h,hll,hs]
  refine ⟨hx,hlog,by linarith only [hll,hs],hupper,?_,?_⟩
  · change (1+L)^3≤_
    calc _ ≤ (2*L)^3 := pow_le_pow_left₀ (by linarith) (by linarith) _
         _ = exp (3*(log 2+u)) := by rw [show (3:ℝ)=(3:ℕ) by norm_num,exp_nat_mul,exp_add,exp_log (by norm_num : 0<(2:ℝ)),exp_log hL]
         _ ≤ _ := exp_le_exp.mpr (by linarith only [log_two_lt_d9,hs,hll])
  · have h₂ : (1:ℝ)/2 ≤ log 2 := by have hh := one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2);norm_num at hh;linarith
    have h := mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg (α:=ℝ) X.primeCounting)
    change log 2/2*(X:ℝ) ≤ X.primeCounting*L at hπ
    nlinarith only [hπ,h,mul_le_mul_of_nonneg_right h₂ hx.le]

#print axioms bounds
end
end Arxiv.«2501.03234».ThetaOccupancyScales
