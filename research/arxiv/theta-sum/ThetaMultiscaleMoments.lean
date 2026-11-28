import ThetaMultiscaleQuantiles
import ThetaEmpiricalPrimeMoments

/-! Logarithmic-square empirical moment bounds at nearly logarithmic orders. -/
namespace Arxiv.«2501.03234».ThetaMultiscaleMoments
open Finset Filter Real ThetaPrimeDensity ThetaPrimeQuantiles ThetaPrimeBandCalibration
noncomputable section

private theorem absorb {X m : ℕ} {M : ℝ} (hM : 0<M) (hw : 1≤width X) (hM' : log M ≤ width X)
    (hL : 0<log (X:ℝ)) (hm : 134217728*(m:ℝ)*(width X)^2 ≤ log X) :
    exp (-(rate X/33554432))*(M*(log X)^2)^m ≤ 1 := by
  have hpow : (M*(log X)^2)^m = exp ((m:ℝ)*(log M+2*log (log X))) := by
    rw [exp_nat_mul,exp_add,show (2:ℝ)=(2:ℕ) by norm_num,exp_nat_mul,exp_log hM,exp_log hL]
  rw [hpow,←exp_add,exp_le_one_iff]
  have hw' : 0<width X := by linarith
  have h₁ : log M+2*log (log X) ≤ 3*width X := by unfold width at *;linarith only [hM']
  have h₂ : (m:ℝ)*(3*width X) ≤ rate X/33554432 := by
    unfold rate;rw [le_div_iff₀ (by norm_num),le_div_iff₀ hw']
    nlinarith only [hm,mul_nonneg (Nat.cast_nonneg (α:=ℝ) m) (sq_nonneg (width X))]
  linarith only [mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg (α:=ℝ) m),h₂]

/-- Uniform bound at all orders m with 2^27 m (1+log log X)^2 ≤ log X. -/
theorem original : ∃ D : ℝ,0<D ∧ ∀ᶠ X : ℕ in atTop,∀ m : ℕ,1≤ m →
    134217728*(m:ℝ)*(1+log (log X))^2 ≤ log X →
    ∑ p∈Nat.primesLE X, |(S p:ℝ)/p-log p/2|^m ≤ Nat.primeCounting X*(D*(1+log (m:ℝ))^2)^m := by
  classical
  obtain ⟨A,hA,hnew⟩ := ThetaMultiscaleExceptions.original_centered
  obtain ⟨C,hC,hold⟩ := ThetaEmpiricalPrimeMoments.logarithmic
  obtain ⟨M,hM,hpt⟩ := pointwise
  let d := max 1 (4*A)
  let D := max C (2*d)
  have hd : 1≤d := le_max_left ..
  have hd' : 0<d := by linarith
  refine ⟨D,hC.trans_le (le_max_left ..),?_⟩
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hnew,hold,hlog.eventually_ge_atTop 1,(tendsto_log_atTop.comp hlog).eventually_ge_atTop (log M)]
    with X hN hO hL hM'
  change 1≤log (X:ℝ) at hL
  change log M ≤ log (log (X:ℝ)) at hM'
  have hw : 1 ≤ width X := by unfold width;linarith only [log_nonneg hL]
  intro m hm hfit
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  let v := (1+log (m:ℝ))^2
  have hv : 1≤v := one_le_pow₀ (by linarith only [log_nonneg hm'])
  have hv' : 0≤v := by linarith
  by_cases hs : (m:ℝ)^2 ≤ log X
  · apply (hO m hm (hs.trans (le_mul_of_one_le_right (le_trans zero_le_one hL) (by linarith only [log_nonneg hm'])))).trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hC.le hv') (mul_le_mul_of_nonneg_right (le_max_left ..) hv') _) (Nat.cast_nonneg _)
  let P := Nat.primesLE X
  let bad (p : ℕ) := A*(width p)^2 ≤ residual p
  let E := P.filter bad
  let G := P.filter (fun p => ¬bad p)
  have hsum := sum_filter_add_sum_filter_not P bad (fun p => residual p^m)
  have hE : (E.card:ℝ) ≤ Nat.primeCounting X*exp (-(rate X/33554432)) := hN
  have hE' : ∑ p∈E,residual p^m ≤ Nat.primeCounting X := by
    have hb := absorb hM hw (by unfold width;linarith only [hM']) (by linarith : 0<log (X:ℝ)) hfit
    calc _ ≤ ∑ _p∈E,(M*(log X)^2)^m := by
           apply sum_le_sum;intro p hp;obtain ⟨hl,hpr⟩ := Nat.mem_primesLE.mp (mem_filter.mp hp).1
           exact pow_le_pow_left₀ (abs_nonneg _) (hpt X p hL hpr hl) m
         _ = (E.card:ℝ)*(M*(log X)^2)^m := by simp
         _ ≤ ((Nat.primeCounting X:ℝ)*exp (-(rate X/33554432)))*(M*(log X)^2)^m :=
           mul_le_mul_of_nonneg_right hE (by positivity)
         _ ≤ _ := by rw [mul_assoc];simpa using mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α:=ℝ) X.primeCounting)
  have hG : ∑ p∈G,residual p^m ≤ (Nat.primeCounting X:ℝ)*(d*v)^m := by
    have hlim := ThetaMultiscaleQuantiles.width_compare (by linarith : 0<log (X:ℝ)) hm' (le_of_not_ge hs)
    calc _ ≤ ∑ _p∈G,(d*v)^m := by
           apply sum_le_sum;intro p hp
           obtain ⟨hh,he⟩ := mem_filter.mp hp;obtain ⟨hl,hpr⟩ := Nat.mem_primesLE.mp hh
           have hh' : residual p ≤ A*(width p)^2 := le_of_not_ge he
           obtain ⟨h₀,h₁⟩ := ThetaMultiscaleQuantiles.width_mono hpr hl
           have hsq := pow_le_pow_left₀ h₀ (h₁.trans hlim) 2
           apply pow_le_pow_left₀ (abs_nonneg _) _ m
           have hdv := mul_le_mul_of_nonneg_right (show 4*A≤d from le_max_right ..) hv'
           dsimp only [v] at *;nlinarith only [mul_le_mul_of_nonneg_left hsq hA.le,hdv,hh']
         _ = (G.card:ℝ)*(d*v)^m := by simp
         _ ≤ _ := by
           apply mul_le_mul_of_nonneg_right _ (by positivity)
           exact_mod_cast (card_filter_le ..).trans_eq (Nat.primesLE_card_eq_primeCounting X)
  have hbase : 1≤d*v := one_le_mul_of_one_le_of_one_le hd hv
  have hpow := one_le_pow₀ (n:=m) hbase
  have ht : (2:ℝ)≤2^m := by simpa only [pow_one] using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hm)
  have hfin : 1+(d*v)^m ≤ (D*v)^m := calc
    _ ≤ (2:ℝ)^m*(d*v)^m := by nlinarith only [hpow,mul_le_mul_of_nonneg_right ht (pow_nonneg (by positivity : 0≤d*v) m)]
    _ = (2*(d*v))^m := (mul_pow ..).symm
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (by rw [←mul_assoc];exact mul_le_mul_of_nonneg_right (le_max_right ..) hv') m
  change ∑ p∈P,residual p^m ≤ (Nat.primeCounting X:ℝ)*(D*v)^m
  change ∑ p∈E,residual p^m + ∑ p∈G,residual p^m = _ at hsum
  linarith only [hE',hG,hsum,mul_le_mul_of_nonneg_left hfin (Nat.cast_nonneg (α:=ℝ) X.primeCounting)]

#print axioms original
end
end Arxiv.«2501.03234».ThetaMultiscaleMoments
