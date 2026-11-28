import ThetaModelExponentialMoment

/-! Tail estimates for each finite reciprocal model with an explicit exposure cutoff. -/
namespace Arxiv.«2501.03234».ThetaFiniteModelTails
open Finset Real Filter ThetaConditionalRows ThetaPrimeTailTransfer ThetaTiltBudget ThetaModelExponentialMoment
noncomputable section

def hit (b x : ℝ) : ℝ := if b < |x| then 1 else 0

theorem height_nonneg (T : ℕ) : 0≤height T := by
  unfold height
  positivity [ThetaSmoothConditionalModel.envelope_nonneg]

theorem cutoff : ∀ᶠ T : ℕ in atTop, ∀ Y V : ℕ, [NeZero Y.factorial] →
    unitMean Y.factorial (fun n => hit (height T+1) (model Y V n)) ≤ 2*exp (total-tilt T) := by
  filter_upwards [model_mgf,eventually_ge_atTop 1] with T hT ht
  intro Y V _
  have hv := tilt_pos (by omega : 0<T)
  by_cases hY : 2≤Y
  · let v := tilt T
    let H := height T+1
    have hp := hT Y V hY v (abs_of_pos hv)
    have hn := hT Y V hY (-v) (by rw [abs_neg,abs_of_pos hv])
    have hpt (z : ℝ) : exp (v*H)*hit H z ≤ exp (v*z)+exp ((-v)*z) := by
      unfold hit
      split_ifs with h
      · rw [mul_one]
        have he := exp_le_exp.mpr (mul_le_mul_of_nonneg_left h.le hv.le)
        rcases le_total 0 z with hz|hz
        · rw [abs_of_nonneg hz] at he
          linarith only [he,exp_pos ((-v)*z)]
        · rw [abs_of_nonpos hz,mul_neg,← neg_mul] at he
          linarith only [he,exp_pos (v*z)]
      · rw [mul_zero]; exact add_nonneg (exp_pos _).le (exp_pos _).le
    have hsum := sum_le_sum (s:=univ) (fun x (_ : x∈(univ : Finset (ZMod Y.factorial)ˣ)) =>
      hpt (model Y V (x:ZMod Y.factorial).val))
    rw [← mul_sum,sum_add_distrib] at hsum
    have hden : 0<(Y.factorial.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.factorial_pos _))
    have he := div_le_div_of_nonneg_right hsum hden.le
    rw [mul_div_assoc,add_div] at he
    have hboth := he.trans (add_le_add hp hn)
    change exp (v*H)*unitMean Y.factorial (fun n => hit H (model Y V n)) ≤ _ at hboth
    have hident : 2*exp (total+tilt T*height T)=2*exp (total-tilt T)*exp (v*H) := by
      rw [mul_assoc,← exp_add];congr 2;dsimp [v,H];ring
    apply (le_of_mul_le_mul_left ?_ (exp_pos (v*H)))
    rw [mul_comm (exp (v*H)) (2*_)]
    apply le_trans hboth
    linarith only [hident]
  · have hem : Icc 2 Y=∅ := Icc_eq_empty_of_lt (by omega)
    have hz (n : ℕ) : model Y V n=0 := by simp [model,ThetaRowCorrelations.low,hem]
    have hn : ¬ (height T+1 < |(0:ℝ)|) := by rw [abs_zero]; linarith [height_nonneg T]
    have he (n : ℕ) : hit (height T+1) (model Y V n)=0 := by rw [hz,hit,if_neg hn]
    simp only [unitMean,he,sum_const_zero,zero_div]
    positivity

#print axioms cutoff
end
end Arxiv.«2501.03234».ThetaFiniteModelTails
