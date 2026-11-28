import ThetaPrimeTailCutoff

/-! Double-exponential upper tails in prime density at every sufficiently large fixed height. -/
namespace Arxiv.«2501.03234».ThetaDoubleExponentialTails
open Real Finset Filter ThetaPrimeTailCutoff ThetaTiltBudget ThetaModelExponentialMoment
open ThetaNaturalPrimeMeans ThetaSmoothConditionalModel ThetaPrimeDensity ThetaDiagonalConstant
noncomputable section

theorem choose_cutoff (P : ℕ → Prop) (hP : ∀ᶠ T in atTop,P T) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ b : ℝ in atTop, ∃ T : ℕ, P T ∧ threshold T≤b ∧
      4*exp (total-tilt T) ≤ exp (-exp (c*sqrt b)) := by
  let K := (8/π^2)*envelope*238
  let D := 8/π^2+1
  let L := 4*(K+1)
  have hK : 0≤K := by dsimp [K];positivity [envelope_nonneg]
  have hL : 0<L := by dsimp [L];linarith
  let u (b : ℝ) := (1/L)*sqrt b
  let t (b : ℝ) := ⌈exp (u b)⌉₊
  have hu : Tendsto u atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by positivity : 0<1/L)).mpr tendsto_sqrt_atTop
  have ht : Tendsto t atTop atTop := tendsto_nat_ceil_atTop.comp (tendsto_exp_atTop.comp hu)
  have hv : Tendsto (fun b => exp (u b/8)) atTop atTop := tendsto_exp_atTop.comp
    ((tendsto_div_const_atTop_of_pos (by norm_num : (0:ℝ)<8)).mpr hu)
  refine ⟨1/(8*L),by positivity,?_⟩
  filter_upwards [ht.eventually hP,hu.eventually_ge_atTop 1,hv.eventually_ge_atTop (|total+log 4|+2),
    eventually_ge_atTop (max 0 (2*D))] with b hT h₁ h₂ hb
  let T := t b
  have he : 1≤exp (u b) := one_le_exp (by linarith)
  have hceil : exp (u b)≤(T:ℝ) := Nat.le_ceil _
  have hceil' : (T:ℝ)≤2*exp (u b) := by
    have h := Nat.ceil_lt_add_one (exp_pos (u b)).le
    change (⌈exp (u b)⌉₊:ℝ)≤_;linarith
  have hpos : 0<(T:ℝ) := lt_of_lt_of_le (exp_pos _) hceil
  have hlog : log T≤2*u b := by
    have h := log_le_log hpos hceil'
    rw [log_mul (by norm_num) (exp_pos _).ne',log_exp] at h
    linarith only [h,h₁,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hsq := pow_le_pow_left₀ (log_nonneg (he.trans hceil)) hlog 2
  have hLu : L*u b=sqrt b := by dsimp [u];field_simp
  have hbu : L^2*(u b)^2=b := by rw [← mul_pow,hLu,Real.sq_sqrt ((le_max_left ..).trans hb)]
  have hlarge : 8*K≤L^2 := by dsimp [L];nlinarith [sq_nonneg K]
  refine ⟨T,hT,?_,?_⟩
  · have hh : threshold T=K*(log T)^2+D := by unfold threshold height K D;ring
    rw [hh]
    nlinarith only [mul_le_mul_of_nonneg_left hsq hK,mul_le_mul_of_nonneg_right hlarge (sq_nonneg (u b)),
      (le_max_right 0 (2*D)).trans hb,hbu]
  · have hl : exp (u b/4)≤tilt T := by
      have h := rpow_le_rpow (exp_pos _).le hceil (by norm_num : (0:ℝ)≤1/4)
      simpa only [tilt,← exp_mul,div_eq_mul_inv,one_mul] using h
    have hs : exp (u b/8)^2=exp (u b/4) := by rw [sq,← exp_add];congr 1;ring
    have hzero : 0≤exp (u b/8)-2 := by linarith [abs_nonneg (total+log 4)]
    have hmax : total+log 4≤exp (u b/8)-2 := by linarith only [le_abs_self (total+log 4),h₂]
    have hgap := mul_nonneg hzero (exp_pos (u b/8)).le
    have heq : 1/(8*L)*sqrt b=u b/8 := by dsimp [u];ring
    rw [heq,← show exp (log (4:ℝ))=4 by exact exp_log (by norm_num),← exp_add]
    apply exp_le_exp.mpr
    nlinarith only [hl,hs,hgap,hmax]

theorem original_prime (hAP : ProgressionMangoldt) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ b : ℝ in atTop, ∀ᶠ X : ℕ in atTop,
      ((primeSet (fun p => b < |(S p:ℝ)/p-log p/2-diagonalConstant|) X).card:ℝ)/X.primeCounting ≤
        exp (-exp (c*sqrt b)) := by
  obtain ⟨c,hc,H⟩ := choose_cutoff _ (cutoff_prime hAP)
  refine ⟨c,hc,?_⟩
  filter_upwards [H] with b hb
  obtain ⟨T,hT,ht,he⟩ := hb
  filter_upwards [hT] with X hX
  have hh : exceptional b X⊆exceptional (threshold T) X := by
    intro p hp
    obtain ⟨hp,hb⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hp,lt_of_le_of_lt ht hb⟩
  exact (div_le_div_of_nonneg_right (Nat.cast_le.mpr (card_le_card hh)) (Nat.cast_nonneg _)).trans (hX.trans he)

#print axioms original_prime
end
end Arxiv.«2501.03234».ThetaDoubleExponentialTails
