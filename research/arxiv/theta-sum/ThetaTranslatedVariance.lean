import ThetaReciprocalLargeSieve
import ThetaDenominatorTails

/-! A translated large-sieve estimate obtained by dyadic denominator bands. -/
namespace Arxiv.«2501.03234».ThetaTranslatedVariance
open Finset Real ThetaReciprocalInversion ThetaReciprocalLargeSieve
noncomputable section

/-- Sum an interval estimate on each dyadic band of primitive frequencies. -/
theorem dyadic {L : ℕ → ℕ} {Y : ℕ} (hY : 0<Y) (M X : ℕ) {V : ℝ}
    (bound : ∀ {R : ℕ}, 0<R → R≤Y → ∀ s : Finset ℕ, (∀ q∈s,R≤q ∧ q≤2*R) →
      ∑ n∈range X,‖windowBand L Y s (M+n)‖^2 ≤ V) :
    ∑ n∈range X,‖windowExtension L Y (M+n)‖^2 ≤ ((Nat.log 2 Y+1:ℕ):ℝ)^2*V := by
  classical
  let J := Nat.log 2 Y+1
  let S (j : ℕ) := (Icc 1 Y).filter (fun q => Nat.log 2 q=j)
  let F (j n : ℕ) := windowBand L Y (S j) (M+n)
  have hdecomp (n : ℕ) : windowExtension L Y (M+n)=∑ j∈range J,F j n := by
    unfold windowExtension F windowBand S
    apply (sum_fiberwise_of_maps_to (s:=Icc 1 Y) (g:=Nat.log 2) (t:=range J) (fun q hq =>
      mem_range.mpr (Nat.lt_succ_of_le (Nat.log_monotone (mem_Icc.mp hq).2))) _).symm
  have hband (j : ℕ) (hj : j∈range J) : ∑ n∈range X,‖F j n‖^2 ≤
      V := by
    have hpow : 2^j≤Y := (Nat.pow_le_pow_right (by decide : 0<2) (by have := mem_range.mp hj;dsimp [J] at this;omega)).trans
      (Nat.pow_log_le_self 2 hY.ne')
    have hh (q : ℕ) (hq : q∈S j) : 2^j≤q ∧ q≤2*2^j := by
      obtain ⟨hq,hj⟩ := mem_filter.mp hq
      rw [← hj]
      refine ⟨Nat.pow_log_le_self 2 (by have := (mem_Icc.mp hq).1;omega),?_⟩
      simpa [pow_succ,mul_comm] using (Nat.lt_pow_succ_log_self (by decide : 1<2) q).le
    exact bound (by positivity) hpow (S j) hh
  have hcs (n : ℕ) : ‖windowExtension L Y (M+n)‖^2 ≤ J*∑ j∈range J,‖F j n‖^2 := by
    rw [hdecomp]
    apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le ..) 2).trans
    simpa using sum_mul_sq_le_sq_mul_sq (range J) (fun _ => (1:ℝ)) (fun j => ‖F j n‖)
  apply (sum_le_sum (s:=range X) (fun n _ => hcs n)).trans
  rw [← mul_sum,sum_comm]
  have hh := sum_le_sum (s:=range J) hband
  apply (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg J (α:=ℝ))).trans_eq
  simp only [sum_const,card_range,nsmul_eq_mul]
  change _= (J:ℝ)^2*V
  ring

#print axioms dyadic
end
end Arxiv.«2501.03234».ThetaTranslatedVariance
