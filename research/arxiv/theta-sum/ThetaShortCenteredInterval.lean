import ThetaShortCenteredDeviation
import ThetaWeilShortIntervals
import ThetaCenteredEndpoint

/-! Centered-moment deviations in every translated interval, with elementary
or complete-Weil input for the endpoint-independent term. -/
namespace Arxiv.«2501.03234».ThetaShortCenteredInterval
open Real Finset Filter ThetaCenteredDeviation ThetaShortPrimeInterval
noncomputable section

theorem absorb {D a : ℝ} (hD : 0<D) (ha : 0<a) (k : ℕ) : ∀ᶠ X : ℕ in atTop,
    D*(1+log X)^k≤exp (a*rate X) := by
  let B := D*2^k
  have hB : 0<B := by dsimp [B];positivity
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hz := tendsto_log_atTop.comp hlog
  have hkp : 0<(k:ℝ)+1 := by positivity
  have hsmall := hlog.eventually ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<3/4)).bound
    (div_pos ha hkp))
  filter_upwards [hsmall,hlog.eventually_ge_atTop 1,hz.eventually_ge_atTop (log B)] with X hs hL hB'
  change 1≤log (X:ℝ) at hL
  change log B≤log (log (X:ℝ)) at hB'
  let L := log (X:ℝ)
  let z := log L
  have hLp : 0<L := by dsimp [L];linarith
  change ‖z‖≤a/((k:ℝ)+1)*‖L^(3/4:ℝ)‖ at hs
  rw [Real.norm_eq_abs,abs_of_nonneg (log_nonneg hL),Real.norm_eq_abs,
    abs_of_nonneg (rpow_nonneg hLp.le _),←rate_eq hLp,div_mul_eq_mul_div,le_div_iff₀ hkp] at hs
  calc _ ≤ D*(2*L)^k := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith)
             (by change 1+log (X:ℝ)≤2*log (X:ℝ);linarith) k) hD.le
       _ = exp (log B+(k:ℝ)*z) := by rw [exp_add,exp_log hB,exp_nat_mul,show exp z=L from exp_log hLp,mul_pow];dsimp [B];ring
       _ ≤ _ := exp_le_exp.mpr (by change log B≤z at hB';linarith only [hs,hB'])

/-- The first term is uniform over interval lengths; the second has spacing
exponent three quarters unconditionally and one half under complete Weil. -/
theorem interval {e : ℕ} (h32 : 32≤e) (h48 : e≤48) (kernel : ThetaCalibratedCone.Kernel e)
    {ε : ℝ} (he : 0<ε) : ∃ a C : ℝ, 0<a ∧ 0<C ∧ ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, H≤X →
    ((primes X H (fun p => ε*(p:ℝ)*log p≤|(S p:ℝ)-p*log p/2|)).card:ℝ) ≤
      (H:ℝ)/log X*exp (-a*(log X)^(3/4:ℝ))+C*(X:ℝ)^((e:ℝ)/64)*(1+log X)^8 := by
  obtain ⟨a,D,ha,_,hD,hb⟩ := ThetaShortCenteredDeviation.band h32 h48 kernel he
  have H := from_band hD (fun N => exp (-a*rate N))
    (fun X => exp (-(a/128)*(log X)^(3/4:ℝ))) (fun _ => (exp_pos _).le) hb
  obtain ⟨C,hC,h⟩ := H (by
    filter_upwards [absorb hD (show 0<a/128 by positivity) 9] with X h
    intro N _ hX hx hLn hLx _
    have hc := ThetaCenteredEndpoint.compare_rate hX hx hLn hLx
    have hn : exp (-a*rate N)≤exp (-(a/64)*rate X) :=
      exp_le_exp.mpr (by linarith only [mul_le_mul_of_nonneg_left hc ha.le])
    apply (mul_le_mul h hn (exp_pos _).le (exp_pos _).le).trans_eq
    rw [←exp_add,←rate_eq (by linarith : 0<log (X:ℝ))]
    congr 1
    ring)
  exact ⟨a/128,C,by positivity,hC,h⟩

theorem elementary {ε : ℝ} (he : 0<ε) : ∃ a C : ℝ, 0<a ∧ 0<C ∧ ∀ᶠ X : ℕ in atTop,
    ∀ H : ℕ, H≤X → ((primes X H (fun p => ε*(p:ℝ)*log p≤|(S p:ℝ)-p*log p/2|)).card:ℝ) ≤
      (H:ℝ)/log X*exp (-a*(log X)^(3/4:ℝ))+C*(X:ℝ)^(3/4:ℝ)*(1+log X)^8 := by
  simpa only [show ((48:ℕ):ℝ)/64=3/4 by norm_num] using
    interval (by decide : 32≤48) (le_refl _) ThetaCalibratedCone.elementary_kernel he

theorem square_root (weil : ThetaWeilShortIntervals.Weil) {ε : ℝ} (he : 0<ε) :
    ∃ a C : ℝ, 0<a ∧ 0<C ∧ ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, H≤X →
    ((primes X H (fun p => ε*(p:ℝ)*log p≤|(S p:ℝ)-p*log p/2|)).card:ℝ) ≤
      (H:ℝ)/log X*exp (-a*(log X)^(3/4:ℝ))+C*sqrt X*(1+log X)^8 := by
  simpa only [show ((32:ℕ):ℝ)/64=1/2 by norm_num,←sqrt_eq_rpow] using
    interval (le_refl 32) (by decide : 32≤48) (ThetaWeilShortIntervals.kernel weil) he

#print axioms elementary
#print axioms square_root
end
end Arxiv.«2501.03234».ThetaShortCenteredInterval
