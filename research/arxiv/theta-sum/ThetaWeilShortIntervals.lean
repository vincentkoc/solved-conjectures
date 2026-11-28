import ThetaShortPrimeInterval
import ThetaSquareRootWindow

/-! A square-root spacing threshold from the classical complete Kloosterman bound. -/
namespace Arxiv.«2501.03234».ThetaWeilShortIntervals
open Finset Filter Real ThetaCalibratedCone ThetaShortPrimeInterval ThetaStrongDeviation ThetaStrongOriginalTail
noncomputable section

/-- The complete Weil estimate, in the normalization of the notebook kernel. -/
def Weil := ∀ (p : ℕ) [Fact p.Prime], ThetaSquareRootWindow.CompleteEstimate p

theorem kernel (weil : Weil) : Kernel 32 := by
  intro N p hp hh a b hb
  apply (weil p a b hb).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have h := sqrt_le_sqrt (show (p:ℝ)≤(N:ℝ)^64 by exact_mod_cast hh)
  rw [show (N:ℝ)^64=((N:ℝ)^32)^2 by ring,sqrt_sq (by positivity)] at h
  exact h

theorem square_root (weil : Weil) : ExceptionalPower (1/2:ℝ) := by
  rw [show (1/2:ℝ)=((32:ℕ):ℝ)/64 by norm_num]
  exact @exceptional_for 32 (by decide) (by decide) (kernel weil)

theorem exceptional (weil : Weil) {ε : ℝ} (hε : 0<ε) : ∃ C : ℝ, 0<C ∧ ∀ᶠ X : ℕ in atTop,
    ∀ H : ℕ, H≤X →
    ((primes X H (fun p => ε*(p:ℝ)*log p≤|(S p:ℝ)-p*log p/2|)).card:ℝ)≤
      H/log X*exp (-rate X/1536)+C*sqrt X*(1+log X)^8 := by
  simpa only [sqrt_eq_rpow] using square_root weil hε

theorem lower (weil : Weil) {c : ℝ} (hc : c<1/2) : ∀ᶠ X : ℕ in atTop, ∀ H : ℕ,
    sqrt X*exp (rate X/512)≤H → H≤X →
    ((primes X H (fun p => (S p:ℝ)≤c*p*log p)).card:ℝ) ≤ (H:ℝ)/log X*exp (-rate X/2048) := by
  simpa only [sqrt_eq_rpow] using lower_of_bound (square_root weil) hc

#print axioms kernel
#print axioms square_root
#print axioms exceptional
#print axioms lower
end
end Arxiv.«2501.03234».ThetaWeilShortIntervals
