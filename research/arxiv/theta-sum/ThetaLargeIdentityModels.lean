import ThetaIdentityHarmonics
import ThetaFactorialSequence
import ThetaIdentityModels

/-! A logarithmic-square lower bound for models on a prescribed sequence of identity classes. -/
namespace Arxiv.«2501.03234».ThetaLargeIdentityModels
open Finset Filter ThetaOddHarmonicTriangle ThetaDivisorLogMean ThetaFactorialSequence
open ThetaRowCorrelations ThetaIdentityFiber ThetaIdentityModels ThetaPrimeMeanSquare ThetaReciprocalInversion
open ThetaConditionalRows ThetaPrimeTailTransfer
noncomputable section

private def capturedValue (T d : ℕ) : ℝ := max (1/2) (if d≤ T then U d-1 else 0)

private theorem captured_mass {T : ℕ} (hT : 2≤ T) :
    mass (modulus T)/8-1/4 + (H T^2/4-H T)/2 ≤
      ∑ d∈(modulus T).divisors.filter (fun d => Odd d ∧ 1< d), capturedValue T d/d := by
  classical
  let m := modulus T
  let G := m.divisors.filter (fun d => Odd d ∧ 1< d)
  let E := (odds T).erase 1
  have hE : E⊆G := by
    intro d hd
    obtain ⟨hne,hd⟩ := mem_erase.mp hd
    obtain ⟨h,ho⟩ := mem_filter.mp hd
    obtain ⟨hl,hr⟩ := mem_Icc.mp h
    have hm := (Nat.dvd_factorial hl hr).trans (dvd_pow_self _ (by omega : T≠0))
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hm,pow_ne_zero _ (Nat.factorial_ne_zero _)⟩,ho,by omega⟩
  have hnon (d) : 0≤ capturedValue T d := (by norm_num : (0:ℝ)≤1/2).trans (le_max_left ..)
  let w (d : ℕ) := capturedValue T d/d
  have hbase : (mass m/2-1)/2 ≤ ∑ d∈G,w d := by
    apply (div_le_div_of_nonneg_right (odd_mass m) (by norm_num : (0:ℝ)≤2)).trans
    rw [sum_div]; apply sum_le_sum; intro d _
    calc _ = (1/2)/(d:ℝ) := by ring
         _ ≤ _ := div_le_div_of_nonneg_right (le_max_left ..) (Nat.cast_nonneg _)
  have hthin : H T^2/4-H T ≤ ∑ d∈G,w d := by
    have h1 : 1∈odds T := mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl,by omega⟩,by decide⟩
    have hsum : ∑ d∈E,(U d-1)/d=(∑ d∈odds T,U d/d)-H T := by
      have hu : U 1=1 := by norm_num [U,odds,Finset.filter_singleton,show Odd (1:ℕ) by decide]
      have h := sum_erase_add (odds T) (fun d => (U d-1)/d) h1
      simp only [hu,sub_self,zero_div,add_zero] at h
      rw [h,H,←sum_sub_distrib]; apply sum_congr rfl; intros; ring
    apply (sub_le_sub_right (triangle T) (H T)).trans
    rw [←hsum]
    apply (sum_le_sum (g:=w) (fun d hd => ?_)).trans (sum_le_sum_of_subset_of_nonneg hE (fun i _ _ => div_nonneg (hnon i) (Nat.cast_nonneg _)))
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg d)
    have h := (mem_Icc.mp (mem_filter.mp (mem_erase.mp hd).2).1).2
    exact (show U d-1 = (if d≤ T then U d-1 else 0) from (if_pos h).symm).trans_le (le_max_right ..)
  change _ ≤ ∑ d∈G,w d
  linarith

theorem growing_models :
    ∀ᶠ T : ℕ in atTop, let m := modulus T
      1 < m ∧ ∀ᶠ Y : ℕ in atTop, ∀ᶠ V : ℕ in atTop,
        letI : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
        m∣Y.factorial ∧ (H T^2/4-H T)/2-1/4 ≤ m.totient*unitMean Y.factorial (fun n => select m n*model Y V n) := by
  have hz : 0≤ Z := tsum_nonneg fun _ => by positivity
  filter_upwards [eventually_ge_atTop (2:ℕ),little (1080*Z) (by positivity) (by norm_num : (0:ℝ)<1/8)] with T hT hB
  let m := modulus T
  have hm : 2≤ m := Nat.le_of_dvd (pow_pos (Nat.factorial_pos _) _) ((Nat.dvd_factorial (by decide : 0<2) hT).trans (dvd_pow_self _ (by omega : T≠0)))
  refine ⟨hm,?_⟩
  filter_upwards [eventually_ge_atTop m] with Y hY
  filter_upwards [eventually_ge_atTop (max m 3)] with V hv
  have hV := (le_max_left m 3).trans hv
  have h3 := (le_max_right m 3).trans hv
  have hu (d : ℕ) (hd : 1< d) (ho : Odd d) (_ : d∣m) : capturedValue T d≤ row d (coneWindow (coneWidth V) d) 1 := by
    have hcw : 2≤ coneWidth V := by dsimp [coneWidth]; omega
    have hx := Nat.mul_le_mul_right d hcw
    have hk : d≤ coneWindow (coneWidth V) d := by simp only [coneWindow,if_neg (by omega : d≠1)]; omega
    have hf := ThetaIdentityRow.lower hd ho (by omega : 0< coneWindow (coneWidth V) d)
    apply max_le hf
    split_ifs
    · exact ThetaIdentityHarmonics.lower hd ho hk
    · linarith
  let : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
  have h := budget hm hY hV (capturedValue T) (fun d => (by norm_num : (0:ℝ)≤1/2).trans (le_max_left ..)) hu (hB Y)
  have hC := captured_mass hT
  refine ⟨Nat.dvd_factorial (by omega) hY,?_⟩
  change _ ≤ (m.totient:ℝ)*_ at h ⊢
  linarith
#print axioms growing_models
end
end Arxiv.«2501.03234».ThetaLargeIdentityModels
