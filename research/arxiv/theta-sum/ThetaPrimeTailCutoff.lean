import ThetaFiniteModelTails
import ThetaPrimeResidualLaw

/-! Finite prime exception counts for the original theta residual. -/
namespace Arxiv.«2501.03234».ThetaPrimeTailCutoff
open Real Finset Filter ThetaFiniteModelTails ThetaModelExponentialMoment ThetaTiltBudget
open ThetaPrimeLaw ThetaPrimeTailTransfer ThetaDiagonalConstant ThetaCharacterPrimeMeans
open ThetaNaturalPrimeMeans ThetaConditionalRows ThetaPrimeDensity ThetaPeriodMeans
noncomputable section
local instance (n : ℕ) : NeZero n.factorial := ⟨Nat.factorial_ne_zero _⟩

def threshold (T : ℕ) := (8/π^2)*(height T+1)+1
def exceptional (t : ℝ) := primeSet (fun p => t < |(S p:ℝ)/p-log p/2-diagonalConstant|)

theorem count_mean (b : ℝ) (X : ℕ) :
    ((exceptional b X).card:ℝ)/X.primeCounting =
      primeMean (fun p => hit b (residual p-diagonalConstant)) X := by
  classical
  unfold exceptional primeSet primeMean
  congr 1
  rw [Finset.card_filter]
  push_cast
  apply sum_congr rfl
  intro p _
  unfold ThetaCharacterPrimeMeans.residual hit
  split_ifs <;> norm_num

theorem cutoff_prime (hAP : ProgressionMangoldt) : ∀ᶠ T : ℕ in atTop, ∀ᶠ X : ℕ in atTop,
    ((exceptional (threshold T) X).card:ℝ)/X.primeCounting ≤ 4*exp (total-tilt T) := by
  filter_upwards [ThetaFiniteModelTails.cutoff] with T hT
  let ε := exp (total-tilt T)
  have hε : 0<ε := exp_pos _
  obtain ⟨Y,V,happrox⟩ := residual_model_approximation hε
  let f (p : ℕ) := hit (height T+1) (model Y V p)
  have hper : OnMod Y.factorial f := by
    have hp : OnMod Y.factorial (model Y V) := ThetaConditionalRows.low_onMod
      (fun d hd _ => Nat.dvd_factorial (by have := (mem_Icc.mp hd).1;omega) (mem_Icc.mp hd).2) _ _
    exact fun n => congrArg (hit (height T+1)) (hp n)
  have hmean := (periodic_prime_mean hAP hper).eventually_le_const
    (show unitMean Y.factorial f < unitMean Y.factorial f+ε by linarith)
  have hb := hT Y V
  change unitMean Y.factorial f ≤ 2*ε at hb
  filter_upwards [happrox,hmean] with X hx hm
  rw [count_mean]
  have hpoint (p : ℕ) : hit (threshold T) (residual p-diagonalConstant) ≤
      |residual p-residualModel Y V p|+f p := by
    by_cases h : threshold T < |residual p-diagonalConstant|
    · simp only [hit,if_pos h]
      by_cases hh : height T+1 < |model Y V p|
      · simp only [f,hit,if_pos hh]
        linarith [abs_nonneg (residual p-residualModel Y V p)]
      · simp only [f,hit,if_neg hh,add_zero]
        have hx := abs_sub_le (residual p) (residualModel Y V p) diagonalConstant
        rw [show residualModel Y V p-diagonalConstant=(8/π^2)*model Y V p by unfold residualModel;ring,
          abs_mul,abs_of_nonneg (by positivity : 0≤8/π^2)] at hx
        unfold threshold at h
        linarith only [hx,h,mul_le_mul_of_nonneg_left (le_of_not_gt hh) (by positivity : 0≤8/π^2)]
    · simp only [hit,if_neg h]
      have hn : 0≤f p := by unfold f hit;split_ifs <;> norm_num
      linarith [abs_nonneg (residual p-residualModel Y V p)]
  have H := mean_mono hpoint X
  rw [mean_add] at H
  change _ ≤ 4*ε
  linarith only [H,hx,hm,hb]

#print axioms count_mean
#print axioms cutoff_prime
end
end Arxiv.«2501.03234».ThetaPrimeTailCutoff
