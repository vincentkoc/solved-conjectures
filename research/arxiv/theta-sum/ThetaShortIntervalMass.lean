import ThetaTranslatedVariance

/-! Separate the diagonal and spacing terms in the translated large sieve. -/
namespace Arxiv.«2501.03234».ThetaShortIntervalMass
open Finset Real ThetaReciprocalBlocks ThetaReciprocalInversion ThetaReciprocalLargeSieve
open ThetaUniformWindows ThetaDenominatorTails ThetaTranslatedVariance
noncomputable section

theorem dyadic_mass : ∃ A : ℝ, 0≤A ∧ ∀ (L : ℕ → ℕ), L 1=0 → ∀ {Y R : ℕ},
    0<R → R≤Y → ∀ s : Finset ℕ, (∀ q∈s,R≤q ∧ q≤2*R) →
    ∑ q∈s,windowMass L Y q≤A*(1+log (2*(Y:ℝ)))^2/R := by
  obtain ⟨C,hC,block⟩ := windowBlock_uniform
  refine ⟨2*C^2,by positivity,?_⟩
  intro L hL Y R hR hRY s hs
  have hr : 0<(R:ℝ) := by exact_mod_cast hR
  have hy : 1≤(Y:ℝ) := by exact_mod_cast hR.trans_le hRY
  let V := 1+log (2*(Y:ℝ))
  have hv : 0≤V := by dsimp [V];linarith only [log_nonneg (by linarith : 1≤2*(Y:ℝ))]
  have hmass (q : ℕ) (hq : q∈s) : windowMass L Y q≤(C*V/R)^2 := by
    obtain ⟨hlo,hhi⟩ := hs q hq
    have hqp := hR.trans_le hlo
    let : NeZero q := ⟨hqp.ne'⟩
    have hq' : 0<(q:ℝ) := by exact_mod_cast hqp
    have hm : windowMass L Y q≤‖windowBlock L Y q‖^2 := by
      simpa only [windowMass,windowCoordinate,dif_neg (NeZero.ne q)] using primitive_mass_le q (windowBlock L Y q)
    apply hm.trans (pow_le_pow_left₀ (norm_nonneg _) ((block L hL Y q).trans ?_) 2)
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add_right (log_le_log hq'
      (show (q:ℝ)≤2*(Y:ℝ) by exact_mod_cast hhi.trans (Nat.mul_le_mul_left 2 hRY))) 1) hC) hq'.le).trans
    exact div_le_div_of_nonneg_left (mul_nonneg hC hv) hr (by exact_mod_cast hlo)
  have hsub : s⊆Icc 1 (2*R) := fun q hq => mem_Icc.mpr ⟨hR.trans_le (hs q hq).1,(hs q hq).2⟩
  have hc : (s.card:ℝ)≤2*(R:ℝ) := by exact_mod_cast (card_le_card hsub).trans_eq (by simp [Nat.card_Icc])
  apply (sum_le_sum hmass).trans
  simp only [sum_const,nsmul_eq_mul]
  change (s.card:ℝ)*_≤2*C^2*V^2/R
  apply (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans_eq
  field_simp

theorem interval : ∃ B A : ℝ, 0≤B ∧ 0≤A ∧ ∀ {T : ℕ}, 1≤T →
    ∀ L : ℕ → ℕ, (∀ d≤T,L d=0) → ∀ {Y : ℕ}, 0<Y → ∀ M H : ℕ,
    ∑ n∈range H,‖windowExtension L Y (M+n)‖^2 ≤ ((Nat.log 2 Y+1:ℕ):ℝ)^2*
      (2*B*H/(T:ℝ)^(1/64:ℝ)+16*A*Y*(1+log (2*(Y:ℝ)))^2*harmonic ((2*Y)^2)) := by
  obtain ⟨B,hB,energy⟩ := cut_energy
  obtain ⟨A,hA,mass⟩ := dyadic_mass
  refine ⟨B,A,hB,hA,?_⟩
  intro T hT L hL Y hY M H
  apply dyadic hY
  intro R hR hRY s hs
  have high := energy hT L hL Y 1 (by decide) s (fun q hq => hR.trans_le (hs q hq).1)
  simp only [Nat.cast_one,one_rpow,div_one] at high
  have raw := mass L (hL 1 hT) hR hRY s hs
  have ht := window_sieve_translate L Y M H (2*R) s (fun q hq =>
    mem_Icc.mpr ⟨hR.trans_le (hs q hq).1,(hs q hq).2⟩)
  let V := (1+log (2*(Y:ℝ)))^2
  let Z := ∑ q∈s,windowMass L Y q
  have hr : 0<(R:ℝ) := by exact_mod_cast hR
  have hh := harmonic_mono_real (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 hRY) 2)
  have hh0 : 0≤(harmonic ((2*R)^2):ℝ) := by simpa using harmonic_mono_real (Nat.zero_le ((2*R)^2))
  have hrpow : (R:ℝ)*Z≤A*V := by linarith only [(le_div_iff₀ hr).mp raw]
  have hsep := mul_le_mul (show (R:ℝ)≤(Y:ℝ) by exact_mod_cast hRY) hh hh0 (Nat.cast_nonneg Y)
  have hprod := (mul_le_mul_of_nonneg_left hrpow (mul_nonneg hr.le hh0)).trans
    (mul_le_mul_of_nonneg_right hsep (mul_nonneg hA (sq_nonneg _)))
  apply ht.trans
  push_cast
  change 2*((H:ℝ)+2*(2*(R:ℝ))^2*harmonic ((2*R)^2))*Z≤_
  change Z≤_ at high
  change _≤2*B*H/(T:ℝ)^(1/64:ℝ)+16*A*Y*V*harmonic ((2*Y)^2)
  rw [div_eq_mul_inv] at high ⊢
  nlinarith only [hprod,mul_le_mul_of_nonneg_left high (Nat.cast_nonneg H (α:=ℝ))]

#print axioms dyadic_mass
#print axioms interval
end
end Arxiv.«2501.03234».ThetaShortIntervalMass
