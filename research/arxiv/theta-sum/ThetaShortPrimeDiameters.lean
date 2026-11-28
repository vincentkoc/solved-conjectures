import ThetaCenteredPrimeRuns
import ThetaRunDiameters

/-! Long consecutive theta-good runs with a bound on their endpoint distance. -/
namespace Arxiv.«2501.03234».ThetaShortPrimeDiameters
open Finset Filter Real ThetaRunDiameters ThetaPrimeRuns ThetaPrimeDensity ThetaShortProgressions
open ThetaCenteredPrimeRuns ThetaBackwardInterval ThetaShortPrimeInterval
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable _

private theorem keep (A : Finset ℕ) (X H : ℕ) (bad : ℕ → Prop) {F J ρ : ℝ}
    (hF : 1≤F) (hJ : 0<J) (hρ : 0<ρ) (hA : ∀ p∈A,p≤X+H) (hH : (H:ℝ)≤A.card*J)
    (hr : (1-3/F)*A.card≤((starts A ⌊F⌋₊ bad).card:ℝ)) :
    (1-ρ-3/F)*A.card≤((boundedStarts A X H ⌊F⌋₊ bad (F*J/ρ)).card:ℝ) := by
  let S : ℝ := (starts A ⌊F⌋₊ bad).card
  let B : ℝ := (boundedStarts A X H ⌊F⌋₊ bad (F*J/ρ)).card
  have hFp : 0<F := by linarith
  have hl : 1≤⌊F⌋₊ := (Nat.le_floor_iff hFp.le).mpr (by simpa using hF)
  have h := lost A X H ⌊F⌋₊ bad (D:=F*J/ρ) hl hA
  change (F*J/ρ)*(S-B)≤(⌊F⌋₊:ℝ)*H at h
  have htail := (mul_le_mul (Nat.floor_le hFp.le) hH (Nat.cast_nonneg H) hFp.le)
  have h₁ : (F*J/ρ)*(S-B)≤F*(A.card*J) := h.trans htail
  have h₂ : S-B≤ρ*A.card := by
    have h₃ := mul_le_mul_of_nonneg_right h₁ hρ.le
    field_simp at h₃
    exact h₃
  change _≤S at hr
  change _≤B
  linarith only [hr,h₂]

/-- For ordinary primes, the allowable diameter is the run length times
a constant multiple of the mean prime spacing. -/
theorem ordinary {ε : ℝ} (hε : 0<ε) : ∃ a : ℝ, 0<a ∧ ∀ ρ : ℝ, 0<ρ →
    ∀ᶠ X : ℕ in atTop, let A := Nat.primesLE X
      let F := depth a X
      (1-ρ-3/F)*A.card ≤ ((boundedStarts A 0 X ⌊F⌋₊ (deviates ε) (F*(2/log 2*log X)/ρ)).card:ℝ) := by
  obtain ⟨a,ha,h⟩ := ThetaCenteredPrimeRuns.ordinary hε
  refine ⟨a,ha,?_⟩
  intro ρ hρ
  have hl := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [h,prime_count_lower,hl.eventually_ge_atTop 1] with X hx hπ hL
  have hlog : 0<log (X:ℝ) := by change 1≤log (X:ℝ) at hL;linarith
  have h2 : 0<log 2 := log_pos (by norm_num)
  apply keep _ 0 X _ (one_le_exp (mul_nonneg ha.le (ThetaCenteredDeviation.rate_pos _).le))
    (by positivity) hρ (fun p hp => by simpa only [zero_add] using (Nat.mem_primesLE.mp hp).1) _ hx
  rw [Nat.primesLE_card_eq_primeCounting]
  calc (X:ℝ) = (2/log 2)*(log 2/2*(X:ℝ)) := by field_simp
       _ ≤ (2/log 2)*(Nat.primeCounting X*log X) := mul_le_mul_of_nonneg_left hπ (by positivity)
       _ = _ := by ring

/-- The same diameter estimate is uniform in every eligible reduced class in
the short window. For q=1 the order is the ordinary consecutive-prime order. -/
theorem progressions (weil : ThetaWeilShortIntervals.Weil) {ε : ℝ} (hε : 0<ε) :
    ∃ a : ℝ, 0<a ∧ ∀ K : ℕ, Ordinary K → ∀ ρ : ℝ, 0<ρ → ∀ᶠ x : ℕ in atTop,
    ∀ q r : ℕ, 0<q → (q:ℝ)≤(log x)^K → r.Coprime q →
    let A := window x (fun p => p ≡ r [MOD q])
    let F := depth a (left x)
    (1-ρ-3/F)*A.card≤((boundedStarts A (left x) (length x) ⌊F⌋₊ (deviates ε)
      (F*(500*q.totient*log x)/ρ)).card:ℝ) := by
  obtain ⟨a,ha,h⟩ := ThetaCenteredPrimeRuns.progressions weil hε
  refine ⟨a,ha,?_⟩
  intro K li ρ hρ
  have hl := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [h K li,li,admissible,hl.eventually_ge_atTop 1] with x hx hc ⟨_,_,hwide,_,_⟩ hL
  intro q r hq hsize hcop
  let A := window x (fun p => p ≡ r [MOD q])
  have hlog : 0<log (x:ℝ) := by change 1≤log (x:ℝ) at hL;linarith
  have hφ : 0<(q.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  apply keep A (left x) (length x) _ (one_le_exp (mul_nonneg ha.le (ThetaCenteredDeviation.rate_pos _).le))
    (by positivity) hρ (fun p hp => (mem_Ioc.mp (mem_primes.mp hp).1).2) _ (hx q r hq hsize hcop)
  have hc' := (div_le_iff₀ (mul_pos hφ hlog)).mp (hc q r hq hsize hcop)
  change (1/250:ℝ)*width x≤(A.card:ℝ)*_ at hc'
  nlinarith only [hc',hwide]

#print axioms ordinary
#print axioms progressions
end
end Arxiv.«2501.03234».ThetaShortPrimeDiameters
