import ThetaMovingOriginalTail

/-! One finite upper bound for fixed and moving values of the theta residual. -/
namespace Arxiv.«2501.03234».ThetaUniformPrimeTails
open Filter Real Finset ThetaMovingOriginalTail
noncomputable section

/-- The threshold H and the starting endpoint are uniform in h. -/
theorem original : ∃ A H : ℝ, 0<A ∧ 1≤H ∧ ∀ᶠ X : ℕ in atTop, ∀ h : ℝ,
    H≤h → 512*h≤log X →
    ((exceptions (A*h^2) X).card:ℝ)≤Nat.primeCounting X*
      exp (-(h*min (exp (h/8)) (sqrt (log X/(128*h))))/512) := by
  obtain ⟨A,D,H,hA,hD,hH,hb⟩ := ThetaMovingOriginalTail.original
  let H' := max H (max 8 (256*log D))
  refine ⟨A,H',hA,hH.trans (le_max_left ..),?_⟩
  filter_upwards [hb] with X hX
  intro h hh hcap
  have hh₀ : H≤h := (le_max_left ..).trans hh
  have h8 : 8≤h := (le_max_left ..).trans ((le_max_right ..).trans hh)
  have hD' : 256*log D≤h := (le_max_right ..).trans ((le_max_right ..).trans hh)
  have hh₁ : 0<h := by linarith
  let q := min (exp (h/8)) (sqrt (log X/(128*h)))
  have hq : 2≤q := by
    apply le_min
    · linarith only [add_one_le_exp (h/8),h8]
    · have he : (2:ℝ)^2≤log X/(128*h) := (le_div_iff₀ (by positivity)).mpr (by linarith only [hcap])
      exact (Real.le_sqrt_of_sq_le he)
  let k := ⌊q⌋₊
  have hk : (k:ℝ)≤q := Nat.floor_le (by linarith)
  have hₖ := Nat.lt_floor_add_one q
  have hk' : q≤2*(k:ℝ) := by change q<(k:ℝ)+1 at hₖ;linarith
  have hk₁ : 1≤k := by exact_mod_cast (show (1:ℝ)≤k by linarith)
  have hmax : (k:ℝ)≤exp (h/8) := hk.trans (min_le_left ..)
  have hL : 0≤log (X:ℝ) := by linarith
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) k) (hk.trans (min_le_right ..)) 2
  rw [Real.sq_sqrt (div_nonneg hL (by positivity))] at hs
  have hsize := (le_div_iff₀ (by positivity : (0:ℝ)<128*h)).mp hs
  have H₁ := hX hh₀ hk₁ hmax (by linarith only [hsize])
  apply H₁.trans
  have hpay : D*exp (-((k:ℝ)*h)/128)≤exp (-(h*q)/512) := by
    rw [←exp_log hD,←exp_add,exp_le_exp]
    have hkh : h≤(k:ℝ)*h := le_mul_of_one_le_left hh₁.le (by exact_mod_cast hk₁)
    nlinarith only [hD',hkh,mul_le_mul_of_nonneg_right hk' hh₁.le]
  calc _ = Nat.primeCounting X*(D*exp (-((k:ℝ)*h)/128)) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left hpay (Nat.cast_nonneg _)

/-- Within the double-exponential regime the only moving-endpoint condition
is explicit. S and the prime normalization are those of the original problem. -/
theorem double_exponential : ∃ A H : ℝ, 0<A ∧ 1≤H ∧ ∀ᶠ X : ℕ in atTop, ∀ h : ℝ,
    H≤h → 128*h*exp (h/4)≤log X →
    ((exceptions (A*h^2) X).card:ℝ)≤Nat.primeCounting X*exp (-(h*exp (h/8))/512) := by
  obtain ⟨A,H,hA,hH,hb⟩ := original
  refine ⟨A,max H 16,hA,hH.trans (le_max_left ..),?_⟩
  filter_upwards [hb] with X hX
  intro h hh hbudget
  have hH' := (le_max_left ..).trans hh
  have h16 : 16≤h := (le_max_right ..).trans hh
  have hp : 0<h := by linarith
  have he : 4≤exp (h/4) := by linarith only [add_one_le_exp (h/4),h16]
  have hcap : 512*h≤log X := by nlinarith only [hbudget,mul_le_mul_of_nonneg_left he (by positivity : 0≤128*h)]
  have hh' := hX h hH' hcap
  have hw : exp (h/8)≤ sqrt (log X/(128*h)) := by
    apply Real.le_sqrt_of_sq_le
    rw [sq,←exp_add,show h/8+h/8=h/4 by ring,le_div_iff₀ (by positivity)]
    linarith only [hbudget]
  simpa only [min_eq_left hw] using hh'

#print axioms original
#print axioms double_exponential
end
end Arxiv.«2501.03234».ThetaUniformPrimeTails
