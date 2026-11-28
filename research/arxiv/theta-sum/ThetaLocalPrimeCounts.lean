import ThetaLocalExcursionCount
import ThetaShortPrimeInterval

/-! The ordinary unweighted short-interval progression input, with an explicit
logarithmic-integral center, and its extension to nonunit residue classes. -/
namespace Arxiv.«2501.03234».ThetaLocalPrimeCounts
open Finset Real Filter MeasureTheory ThetaShortPrimeInterval ThetaRowProgressionDiscrepancy
noncomputable section

def mass (X H : ℕ) := ∫ t in (X:ℝ)..((X:ℝ)+H), (log t)⁻¹
def sample (X H : ℕ) := primes X H (fun _ => True)

/-- An ordinary short-interval Siegel--Walfisz estimate. The endpoint,
length, and moduli occur only in prime counts. -/
def Ordinary (θ : ℝ) := ∀ A B : ℕ, ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, H≤X → (X:ℝ)^θ≤H →
    ∀ q : ℕ, 0 < q → (q:ℝ)≤(log X)^A → ∀ b < q, b.Coprime q →
      |(((sample X H).filter (fun p => p%q=b)).card:ℝ)-mass X H/q.totient|≤H/(log X)^B

theorem mass_lower {X H : ℕ} (hX : 2≤X) (hH : H≤X) :
    (H:ℝ)/(2*log X)≤ mass X H := by
  have hx : (2:ℝ)≤X := by exact_mod_cast hX
  have hx₀ : 0<(X:ℝ) := by linarith
  have hl : 0<log (X:ℝ) := log_pos (by linarith)
  have ha : (X:ℝ)≤X+H := by linarith [Nat.cast_nonneg (α:=ℝ) H]
  have h₀ : IntervalIntegrable (fun t : ℝ => (log t)⁻¹) volume (X:ℝ) (X+H) := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le ha] at ht
    have hp : 1<t := by linarith only [hx,ht.1]
    exact ((continuousAt_log (by linarith : t≠0)).inv₀ (log_pos hp).ne').continuousWithinAt
  have h := intervalIntegral.integral_mono_on ha (f:=fun _ : ℝ => (2*log X)⁻¹) (by simp) h₀ (fun t ht => by
    have hp : 1<t := by linarith only [hx,ht.1]
    apply inv_anti₀ (log_pos hp)
    have hh := ht.2.trans (show (X:ℝ)+H≤X*X by nlinarith only [(Nat.cast_le.mpr hH : (H:ℝ)≤X),mul_le_mul_of_nonneg_right hx hx₀.le])
    have H := log_le_log (by linarith : 0<t) hh
    rw [log_mul hx₀.ne' hx₀.ne'] at H; linarith)
  simpa [mass,intervalIntegral.integral_const,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using h

theorem classes {θ : ℝ} (h : Ordinary θ) (A B : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, H≤X → (X:ℝ)^θ≤H →
    ∀ q : ℕ, 0 < q → (q:ℝ)≤(log X)^A →
    Classes (sample X H) q (mass X H) (H/(log X)^B) := by
  have hpow := (isLittleO_log_rpow_rpow_atTop (A:ℝ) (by norm_num : (0:ℝ)<1)).bound
    (show (0:ℝ)<1 by norm_num)
  filter_upwards [h A B,(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually hpow,eventually_ge_atTop (2:ℕ)] with X hc hpow hx
  intro H hH hθ q hq hqL b hb
  rw [rpow_one] at hpow
  have hl : 0≤log (X:ℝ) := log_nonneg (by exact_mod_cast (show 1≤X by omega))
  have hqX : q≤X := by
    simp only [rpow_natCast,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hl _),abs_of_nonneg (Nat.cast_nonneg X : (0:ℝ)≤X),one_mul] at hpow
    exact_mod_cast hqL.trans hpow
  by_cases hbc : b.Coprime q
  · rw [if_pos hbc]; exact hc H hH hθ q hq hqL b hb hbc
  · rw [if_neg hbc,sub_zero]
    have he : ((sample X H).filter (fun p => p%q=b))=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp; obtain ⟨hs,hr⟩ := mem_filter.mp hp
      obtain ⟨hI,hpr,_⟩ := mem_primes.mp hs
      have hic := (mem_Ioc.mp hI).1
      have hpq := hpr.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hq (hqX.trans_lt hic))
      exact hbc (hr ▸ (by rwa [←ZMod.isUnit_iff_coprime,ZMod.natCast_mod,ZMod.isUnit_iff_coprime] : (p%q).Coprime q))
    rw [he,card_empty,Nat.cast_zero,abs_zero]; positivity

#print axioms mass_lower
#print axioms classes
end
end Arxiv.«2501.03234».ThetaLocalPrimeCounts
