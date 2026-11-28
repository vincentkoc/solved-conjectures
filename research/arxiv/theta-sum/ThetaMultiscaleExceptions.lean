import ThetaMultiscaleEndpoint

/-! Almost-linear logarithmic exceptional-set savings for the original integer theta sum. -/
namespace Arxiv.«2501.03234».ThetaMultiscaleExceptions
open Filter Real ThetaPrimeDensity ThetaPrimeBandCalibration
noncomputable section

/-- The threshold constant is absolute. Counts and normalization both range over primes up to X. -/
theorem original_centered : ∃ A : ℝ,0<A ∧ ∀ᶠ X : ℕ in atTop,
    ((primeSet (fun p => A*(1+log (log p))^2 ≤ |(S p:ℝ)/p-log p/2|) X).card:ℝ) ≤
      Nat.primeCounting X*exp (-(log X/(1+log (log X))/33554432)) := by
  obtain ⟨A,hA,ht⟩ := ThetaMultiscaleEndpoint.transfer
  exact ⟨A,hA,ht _ (Eventually.of_forall (fun _ _ hh => hh))⟩

private theorem forces {A : ℝ} (hA : 0<A) (k : ℕ) :
    ∀ᶠ p : ℕ in atTop,p.Prime → S p ≤ (k:ℤ)*p → A*(width p)^2 ≤ |(S p:ℝ)/p-log p/2| := by
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have h := hlog.eventually ((isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ)<1)).bound
    (show 0<1/(16*A) by positivity))
  filter_upwards [h,(tendsto_log_atTop.comp hlog).eventually_ge_atTop 1,hlog.eventually_ge_atTop (4*(k:ℝ)+1)]
    with p he hw hk hpr hs
  change ‖(log (log (p:ℝ)))^(2:ℝ)‖ ≤ 1/(16*A)*‖(log (p:ℝ))^(1:ℝ)‖ at he
  change 1≤log (log (p:ℝ)) at hw
  change 4*(k:ℝ)+1 ≤ log (p:ℝ) at hk
  have hl := ThetaDivisorLogMean.log_nonneg_nat p
  rw [show (2:ℝ)=(2:ℕ) by norm_num,rpow_natCast,rpow_one,Real.norm_of_nonneg (sq_nonneg _),
    Real.norm_of_nonneg hl] at he
  have hmul := mul_le_mul_of_nonneg_left he (show 0≤16*A by positivity)
  have hcancel : 16*A*(1/(16*A)*log p)=log p := by field_simp
  have hsq := pow_le_pow_left₀ (by linarith only [hw] : (0:ℝ) ≤ 1+log (log p))
    (by linarith only [hw] : 1+log (log p) ≤ 2*log (log p)) 2
  have hA' := mul_le_mul_of_nonneg_left hsq hA.le
  have hp : 0<(p:ℝ) := by exact_mod_cast hpr.pos
  have hs' : (S p:ℝ)/p ≤ k := (div_le_iff₀ hp).mpr (by exact_mod_cast hs)
  unfold width
  linarith only [hA',hmul,hcancel,hk,hs',neg_le_abs ((S p:ℝ)/p-log p/2)]

/-- Every fixed natural slope in the pinned conjecture 4.4 has the same saving constant. -/
theorem original_slope (k : ℕ) : ∀ᶠ X : ℕ in atTop,
    ((primeSet (fun p => S p ≤ (k:ℤ)*p) X).card:ℝ) ≤
      Nat.primeCounting X*exp (-(log X/(1+log (log X))/33554432)) := by
  obtain ⟨_,hA,ht⟩ := ThetaMultiscaleEndpoint.transfer
  exact ht _ (forces hA k)

/-- Exceptional primes for the strict positivity in conjecture 1.1. -/
theorem original_nonpositive : ∀ᶠ X : ℕ in atTop,((primeSet (fun p => S p ≤ 0) X).card:ℝ) ≤
    Nat.primeCounting X*exp (-(log X/(1+log (log X))/33554432)) := by
  simpa using original_slope 0

#print axioms original_centered
#print axioms original_slope
#print axioms original_nonpositive
end
end Arxiv.«2501.03234».ThetaMultiscaleExceptions
