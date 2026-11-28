import ThetaMultiscaleExceptions
import ThetaPrimeQuantiles

/-! Simultaneous finite square-logarithmic quantiles into the multiscale range. -/
namespace Arxiv.«2501.03234».ThetaMultiscaleQuantiles
open Finset Filter Real ThetaPrimeDensity ThetaPrimeQuantiles ThetaPrimeBandCalibration
noncomputable section

theorem width_mono {p X : ℕ} (hp : p.Prime) (h : p≤X) : 0 ≤ width p ∧ width p ≤ width X := by
  have h₂ : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpos : 0 < log (p:ℝ) := log_pos (by linarith)
  have hlog : log 2 ≤ log (p:ℝ) := log_le_log (by norm_num) h₂
  have hh := log_le_log (by norm_num : (0:ℝ)<1/2) (show 1/2 ≤ log (p:ℝ) by linarith only [log_two_gt_d9,hlog])
  rw [one_div,log_inv] at hh
  unfold width
  exact ⟨by linarith only [log_two_lt_d9,hh],by
    have hle := log_le_log hpos (log_le_log (by positivity : 0<(p:ℝ)) (by exact_mod_cast h : (p:ℝ) ≤ X))
    linarith only [hle]⟩

theorem width_compare {x t : ℝ} (hx : 0 < log x) (_ht : 1 ≤ t) (h : log x ≤ t^2) :
    width x ≤ 2*(1+log t) := by
  have he := log_le_log hx h
  rw [log_pow] at he
  unfold width;norm_num at he ⊢;linarith only [he]

theorem member {Q : ℕ → Prop} {X p : ℕ} : p∈primeSet Q X ↔ p≤X ∧ p.Prime ∧ Q p := by
  classical simp only [primeSet,mem_filter,Nat.mem_primesLE,and_assoc]

/-- One endpoint works for every admissible real tail parameter. -/
theorem original : ∃ D : ℝ,0<D ∧ ∀ᶠ X : ℕ in atTop,∀ t : ℝ,1≤t → t≤rate X/33554432 →
    ((primeSet (fun p => D*(1+log t)^2 ≤ |(S p:ℝ)/p-log p/2|) X).card:ℝ) ≤ Nat.primeCounting X*exp (-t) := by
  classical
  obtain ⟨A,hA,hnew⟩ := ThetaMultiscaleExceptions.original_centered
  obtain ⟨C,hC,hold⟩ := ThetaPrimeQuantiles.original
  let D := max (2*C) (4*A)
  have hD : 0 < D := (by positivity : 0<2*C).trans_le (le_max_left ..)
  refine ⟨D,hD,?_⟩
  filter_upwards [hnew,hold,(tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_gt_atTop 0]
    with X hN hO hL
  change 0<log (X:ℝ) at hL
  intro t ht hfit
  have ht' := log_nonneg ht
  have hv : 1≤(1+log t)^2 := one_le_pow₀ (by linarith)
  by_cases hs : t^2 ≤ log X
  · have hz : t^2/log X ≤ 1 := (div_le_one hL).mpr hs
    have hsq := pow_le_pow_left₀ (div_nonneg (sq_nonneg t) hL.le) hz 2
    have hsub : primeSet (fun p => D*(1+log t)^2 ≤ residual p) X ⊆ ThetaMovingOriginalTail.exceptions (C*height (log X) t) X := by
      intro p hp
      obtain ⟨hl,hp,he⟩ := member.mp hp
      apply ThetaPrimeQuantiles.member.mpr ⟨hl,hp,?_⟩
      have hD' := mul_le_mul_of_nonneg_right (show 2*C ≤ D from le_max_left ..) (sq_nonneg (1+log t))
      dsimp only [height];nlinarith only [hsq,hv,mul_le_mul_of_nonneg_left (hsq.trans (show (1:ℝ)^2 ≤ (1+log t)^2 by simpa using hv)) hC.le,hD',he]
    exact (Nat.cast_le.mpr (card_le_card hsub)).trans (hO t ht)
  · have hsub : primeSet (fun p => D*(1+log t)^2 ≤ residual p) X ⊆ primeSet (fun p => A*(width p)^2 ≤ residual p) X := by
      intro p hp
      obtain ⟨hl,hp,he⟩ := member.mp hp
      obtain ⟨h₀,h₁⟩ := width_mono hp hl
      have hsq := pow_le_pow_left₀ h₀ (h₁.trans (width_compare hL ht (le_of_not_ge hs))) 2
      apply member.mpr ⟨hl,hp,?_⟩
      nlinarith only [mul_le_mul_of_nonneg_left hsq hA.le,mul_le_mul_of_nonneg_right (show 4*A≤D from le_max_right ..) (sq_nonneg (1+log t)),he]
    apply ((Nat.cast_le.mpr (card_le_card hsub)).trans hN).trans
    exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (neg_le_neg hfit)) (Nat.cast_nonneg _)

#print axioms original
end
end Arxiv.«2501.03234».ThetaMultiscaleQuantiles
