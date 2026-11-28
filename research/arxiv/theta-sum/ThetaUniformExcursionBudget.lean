import ThetaExceptionalConductor
import ThetaIdentityModels
import ThetaCompactModulus
import ThetaEmpiricalPrimeMoments

/-! Uniform prime second moment and progression costs below the exceptional-character radius. -/
namespace Arxiv.«2501.03234».ThetaUniformExcursionBudget
open Real Filter Finset ThetaIdentityModels ThetaExceptionalPrimeInput ThetaExceptionalConductor
noncomputable section
set_option exponentiation.threshold 1024

theorem log_lift {T f : ℕ} (hf : 0<f) :
    log (lift (ThetaCompactModulus.modulus T) f:ℝ) ≤ 18480*(T:ℝ) := by
  let m := ThetaCompactModulus.modulus T
  have hm := ThetaCompactModulus.positive T
  obtain ⟨_,hm',hl⟩ := bounds hm hf
  have hh := log_le_log (Nat.cast_pos.mpr (hm.trans_le hm')) (by exact_mod_cast hl : (lift m f:ℝ) ≤ (m:ℝ)^770)
  rw [log_pow] at hh
  have h4 : log (4:ℝ)≤2 := by
    rw [show (4:ℝ)=2^2 by norm_num,log_pow];norm_num;linarith only [log_two_lt_d9]
  have he := ThetaCompactModulus.size T
  change log (m:ℝ) ≤ _ at he
  norm_num only [Nat.cast_ofNat] at hh
  linarith only [hh,he,mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg (α:=ℝ) T)]

theorem energy : ∃ D : ℝ,0<D ∧ ∀ᶠ N : ℕ in atTop,
    (∑ p∈ThetaSiegelWalfiszBand.band N,((S p:ℝ)/p-log p/2)^2) ≤ D*((N:ℝ)^64/log N) := by
  obtain ⟨C,hC,he⟩ := ThetaEmpiricalPrimeMoments.logarithmic
  let K := (C*(1+log 2)^2)^2
  have hK : 0<K := by dsimp [K];positivity [log_pos (by norm_num : (1:ℝ)<2)]
  have h4 := log_pos (by norm_num : (1:ℝ)<4)
  refine ⟨(log 4+1)*K,by positivity,?_⟩
  have hx := tendsto_pow_atTop (α:=ℕ) (n:=64) (by decide)
  have hu := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (Chebyshev.eventually_primeCounting_le zero_lt_one)
  simp only [Nat.floor_natCast] at hu
  have hl := (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  filter_upwards [hx.eventually he,hx.eventually hu,hl] with N he hu hL
  change 1≤log (N:ℝ) at hL
  have hp : 0<log (N:ℝ) := by linarith
  have hln : log ((N^64:ℕ):ℝ)=64*log (N:ℝ) := by rw [Nat.cast_pow,log_pow];norm_num
  have hf : (2:ℝ)^2 ≤ log ((N^64:ℕ):ℝ)*(1+log 2) := by
    rw [hln];nlinarith only [hL,mul_nonneg hp.le (log_nonneg (by norm_num : (1:ℝ)≤2))]
  have hs := he 2 (by decide) (by simpa only [Nat.cast_ofNat] using hf)
  simp only [Nat.cast_ofNat,sq_abs] at hs
  have hsub : ThetaSiegelWalfiszBand.band N ⊆ Nat.primesLE (N^64) := filter_subset _ _
  apply ((sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => sq_nonneg _)).trans hs).trans
  change _*(K) ≤ _
  rw [hln,Nat.cast_pow] at hu
  have hi := (le_div_iff₀ (by positivity)).mp hu
  rw [←mul_div_assoc,le_div_iff₀ hp]
  nlinarith only [mul_le_mul_of_nonneg_right hi hK.le,
    mul_nonneg (Nat.cast_nonneg (α:=ℝ) (N^64).primeCounting) (mul_nonneg hp.le hK.le)]

theorem budgets {κ D : ℝ} (hκ : 0<κ) : ∃ N₀ : ℕ,∀ᶠ T : ℕ in atTop,
    ∀ N≥N₀,∀ f : ℕ,0<f → 134217728*(T:ℝ) ≤ (log (N:ℝ))^(1/3:ℝ) →
    let l := lift (ThetaCompactModulus.modulus T) f
    1 ≤ κ*(l:ℝ) ∧ (3+18*Z)*log N*(l:ℝ)^2048 ≤ κ*radius N ∧
    D/κ^2*(l:ℝ)^6 ≤ exp (131072*(T:ℝ)) := by
  have hl := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hlo := hl.eventually ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/3)).bound (by norm_num : (0:ℝ)<1/2))
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (hlo.and (hl.eventually_ge_atTop 1))
  refine ⟨N₀,?_⟩
  have ht := tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ht.eventually_ge_atTop ((3+18*Z)/κ),ht.eventually_ge_atTop (D/κ^2),
    (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (1/κ),eventually_ge_atTop 1] with T hc hm hT h₁ N hN f hf had l
  obtain ⟨hsmall,hL⟩ := hN₀ N hN
  change 1≤log (N:ℝ) at hL
  have hpL : 0<log (N:ℝ) := by linarith
  let R := (log (N:ℝ))^(1/3:ℝ)
  have heL : log (N:ℝ) ≤ exp (R/2) := by
    rw [←exp_log hpL,exp_le_exp]
    change ‖log (log (N:ℝ))‖≤1/2*‖R‖ at hsmall
    rw [Real.norm_of_nonneg (log_nonneg hL),Real.norm_of_nonneg (rpow_nonneg hpL.le _)] at hsmall
    linarith only [hsmall]
  let m := ThetaCompactModulus.modulus T
  have hp := ThetaCompactModulus.positive T
  obtain ⟨_,hml,_⟩ := bounds hp hf
  have hl' : 0<(l:ℝ) := Nat.cast_pos.mpr (hp.trans_le hml)
  have hTL : T≤l := (Nat.le_of_dvd hp (ThetaCompactModulus.contains h₁ le_rfl)).trans hml
  have hu (j : ℕ) : (l:ℝ)^j ≤ exp ((j:ℝ)*(18480*(T:ℝ))) := by
    rw [←exp_log hl',←exp_nat_mul,exp_le_exp]
    exact mul_le_mul_of_nonneg_left (log_lift hf) (Nat.cast_nonneg _)
  change (3+18*Z)/κ ≤ exp (T:ℝ) at hc
  change D/κ^2 ≤ exp (T:ℝ) at hm
  change 1/κ ≤ (T:ℝ) at hT
  change 134217728*(T:ℝ) ≤ R at had
  constructor
  · have hh := (div_le_iff₀ hκ).mp (hT.trans (Nat.cast_le.mpr hTL));linarith only [hh]
  constructor
  · have hh := mul_le_mul (mul_le_mul hc heL hpL.le (exp_pos _).le) (hu 2048) (pow_nonneg hl'.le _) (by positivity)
    rw [←exp_add,←exp_add] at hh
    have hy : (T:ℝ)+R/2+2048*(18480*(T:ℝ)) ≤ R := by linarith only [had,Nat.cast_nonneg (α:=ℝ) T]
    have h := hh.trans (exp_le_exp.mpr hy)
    change _ ≤ κ*exp _
    rw [←div_le_iff₀' hκ];convert h using 1; ring
  · have hh := mul_le_mul hm (hu 6) (pow_nonneg hl'.le _) (exp_pos _).le
    rw [←exp_add] at hh
    exact hh.trans (exp_le_exp.mpr (by norm_num;linarith only [Nat.cast_nonneg (α:=ℝ) T]))

#print axioms energy
#print axioms budgets
end
end Arxiv.«2501.03234».ThetaUniformExcursionBudget
