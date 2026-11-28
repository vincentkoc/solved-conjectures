import ThetaShortIntervalMass

/-! Logarithmic losses and the polynomial interval length at the prime cutoff. -/
namespace Arxiv.«2501.03234».ThetaShortIntervalEnergy
open Finset Real ThetaReciprocalInversion ThetaDenominatorTails ThetaTranslatedVariance
noncomputable section

theorem scale {N : ℕ} (hN : 1≤N) :
    ((Nat.log 2 (2*N^52)+1:ℕ):ℝ) ≤ 108*(1+log N) ∧
    (harmonic ((2*(2*N^52))^2):ℝ)≤110*(1+log N) ∧
    1+log (2*((2*N^52:ℕ):ℝ)) ≤ 55*(1+log N) := by
  let Y := 2*N^52
  have hNp : 0<(N:ℝ) := by exact_mod_cast hN
  have hy : 0<Y := by dsimp [Y];positivity
  have hL := log_nonneg (show 1≤(N:ℝ) by exact_mod_cast hN)
  have hylog : log (Y:ℝ)=log 2+52*log N := by
    dsimp [Y];push_cast;rw [log_mul (by norm_num) (pow_pos hNp _).ne',log_pow];norm_num
  have hj := Nat.pow_log_le_self 2 hy.ne'
  have hm := log_le_log (by positivity : 0<(2:ℝ)^(Nat.log 2 Y)) (show (2:ℝ)^(Nat.log 2 Y)≤(Y:ℝ) by exact_mod_cast hj)
  rw [log_pow,hylog] at hm
  have hh := harmonic_le_one_add_log ((2*Y)^2)
  rw [Nat.cast_pow,log_pow,Nat.cast_mul,Nat.cast_ofNat,log_mul (by norm_num) (by exact_mod_cast hy.ne'),hylog] at hh
  refine ⟨?_,?_,?_⟩
  · change ((Nat.log 2 Y+1:ℕ):ℝ)≤_
    push_cast
    nlinarith only [hm,log_two_gt_d9,log_two_lt_d9,hL,
      mul_le_mul_of_nonneg_left (show (1/2:ℝ)≤log 2 by linarith [log_two_gt_d9]) (Nat.cast_nonneg (Nat.log 2 Y))]
  · linarith only [hh,log_two_lt_d9,hL]
  · change 1+log (2*(Y:ℝ))≤_
    rw [log_mul (by norm_num) (by exact_mod_cast hy.ne'),hylog]
    linarith only [log_two_lt_d9,hL]

theorem cut : ∃ C : ℝ, 0<C ∧ ∀ {T : ℕ}, 1≤T → ∀ L : ℕ → ℕ, (∀ d≤T,L d=0) →
    ∀ {N J : ℕ}, 1≤N → 0<J → J≤N^52 → ∀ M H : ℕ,
    ∑ n∈range H,‖windowExtension L (2*J) (M+n)‖^2 ≤
      C*(1+log N)^5*((H:ℝ)/(T:ℝ)^(1/64:ℝ)+(J:ℝ)) := by
  obtain ⟨B,A,hB,hA,raw⟩ := ThetaShortIntervalMass.interval
  refine ⟨108^2*(2*B+3520*55^2*A+1),by positivity,?_⟩
  intro T hT L hL N J hN hJpos hcap M H
  let Y := 2*J
  let V := 1+log (N:ℝ)
  let E := (H:ℝ)/(T:ℝ)^(1/64:ℝ)
  let U := (J:ℝ)
  have he : 0≤E := by dsimp [E];positivity
  have hu : 0≤U := by dsimp [U];positivity
  have hl := log_nonneg (show 1≤(N:ℝ) by exact_mod_cast hN)
  have hv : 1≤V := by dsimp [V];linarith
  have hv' : 0≤V := by linarith
  have hy : 0<Y := by dsimp [Y];positivity
  have hh := raw hT L hL hy M H
  have hcap' : Y≤2*N^52 := Nat.mul_le_mul_left 2 hcap
  obtain ⟨hj0,hh0,hl0⟩ := scale hN
  have hJ : ((Nat.log 2 Y+1:ℕ):ℝ)≤108*V :=
    (show ((Nat.log 2 Y+1:ℕ):ℝ)≤((Nat.log 2 (2*N^52)+1:ℕ):ℝ) by
      exact_mod_cast Nat.succ_le_succ (Nat.log_mono_right hcap')).trans hj0
  have hhar := (ThetaReciprocalBlocks.harmonic_mono_real
    (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 hcap') 2)).trans hh0
  have hlog := (add_le_add_right (log_le_log (by positivity : 0<2*(Y:ℝ)) (mul_le_mul_of_nonneg_left
    (show (Y:ℝ)≤((2*N^52:ℕ):ℝ) by exact_mod_cast hcap') (by norm_num : (0:ℝ)≤2))) 1).trans hl0
  have hY : (Y:ℝ)=2*U := by dsimp [Y,U];push_cast;ring
  have hlog0 : 0≤1+log (2*(Y:ℝ)) := by
    have hy' : 1≤(Y:ℝ) := by exact_mod_cast hy
    linarith only [log_nonneg (by linarith : 1≤2*(Y:ℝ))]
  have hhar0 : 0≤(harmonic ((2*Y)^2):ℝ) := by
    simpa using ThetaReciprocalBlocks.harmonic_mono_real (Nat.zero_le ((2*Y)^2))
  have hE : 2*B*H/(T:ℝ)^(1/64:ℝ)=2*B*E := by dsimp [E];ring
  have hterm := mul_le_mul (pow_le_pow_left₀ hlog0 hlog 2) hhar hhar0 (sq_nonneg _)
  have hterm' := mul_le_mul_of_nonneg_left hterm (show 0≤16*A*(Y:ℝ) by positivity)
  rw [hY] at hterm'
  let D := 3520*55^2*A
  have hD : 0≤D := by dsimp [D];positivity
  have h2 : 16*A*(Y:ℝ)*(1+log (2*(Y:ℝ)))^2*harmonic ((2*Y)^2)≤D*U*V^3 := by
    dsimp [D];rw [hY];linarith only [hterm']
  have hfactor : 2*B*E+D*U*V^3 ≤ (2*B+D+1)*V^3*(E+U) := by
    have hv3 := one_le_pow₀ (n:=3) hv
    have hV3 : 0≤V^3 := pow_nonneg hv' _
    nlinarith only [mul_le_mul_of_nonneg_left hv3 (mul_nonneg (by positivity : 0≤2*B) he),
      mul_nonneg (mul_nonneg hB hu) hV3,mul_nonneg (mul_nonneg hD he) hV3,
      mul_nonneg hV3 (add_nonneg he hu)]
  apply hh.trans
  rw [hE]
  apply (mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hJ 2)
    ((add_le_add_right h2 (2*B*E)).trans hfactor) (by positivity) (sq_nonneg _)).trans_eq
  change (108*V)^2*((2*B+D+1)*V^3*(E+U))=108^2*(2*B+D+1)*V^5*(E+U)
  ring

#print axioms cut
end
end Arxiv.«2501.03234».ThetaShortIntervalEnergy
