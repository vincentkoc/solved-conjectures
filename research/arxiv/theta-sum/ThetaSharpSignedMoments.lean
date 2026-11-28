import ThetaUniformLowerQuantiles
import ThetaFiniteLowerMoments
import ThetaMultiscaleMoments

/-! Sharp positive and negative empirical prime moments up to nearly logarithmic orders. -/
namespace Arxiv.«2501.03234».ThetaSharpSignedMoments
open Filter Finset Real ThetaUniformExcursionEndpoint ThetaFiniteLowerMoments
noncomputable section

private theorem moment_from_hits {X k q r : ℕ} {z h : ℝ} (hh : 0≤h)
    (H : (X.primeCounting:ℝ)*exp (-(k:ℝ)) ≤ ((primes X q r z h).card:ℝ)) :
    (X.primeCounting:ℝ)*(exp (-1)*h)^k ≤ oneSidedMoment q r z X k := by
  let G := primes X q r z h
  have hfrac : (X.primeCounting:ℝ)*(exp (-1))^k ≤ (G.card:ℝ) := by
    rw [←exp_nat_mul, mul_neg_one]
    exact H
  have hsub : G⊆(Nat.primesLE X).filter (fun p => p%q=r) := fun p hp =>
    mem_filter.mpr ⟨(mem_filter.mp hp).1,(mem_filter.mp hp).2.1⟩
  rw [mul_pow,←mul_assoc]
  apply (mul_le_mul_of_nonneg_right hfrac (pow_nonneg hh _)).trans
  rw [←nsmul_eq_mul,←sum_const]
  apply (sum_le_sum (s:=G) (g:=fun p => (max 0 (z*((S p:ℝ)/p-log p/2)))^k) (fun p hp =>
    pow_le_pow_left₀ hh ((mem_filter.mp hp).2.2.trans (le_max_right ..)) _)).trans
  exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => pow_nonneg (le_max_left ..) _)


theorem matching (H : ThetaExceptionalPrimeInput.Ordinary) :
    ∃ D δ : ℝ,0<D ∧ 0<δ ∧ ∃ k₀ : ℕ,∀ᶠ X : ℕ in atTop,
    ∀ k≥k₀,134217728*(k:ℝ)*(1+log (log X))^2 ≤ log X →
    ∀ q r : ℕ,0<q → r<q → r.Coprime q → log q ≤ δ*log k →
    ∀ z : ℝ,|z|=1 →
      (X.primeCounting:ℝ)*(exp (-1)*((1+log k)^2/(16384*π^2)))^k ≤ oneSidedMoment q r z X k ∧
      oneSidedMoment q r z X k ≤ (X.primeCounting:ℝ)*(D*(1+log k)^2)^k := by
  obtain ⟨δ,hδ,t₀,hlow⟩ := ThetaUniformLowerQuantiles.original H
  obtain ⟨D,hD,hup⟩ := ThetaMultiscaleMoments.original
  refine ⟨D,δ,hD,hδ,max ⌈t₀⌉₊ 1,?_⟩
  have hL := (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  filter_upwards [hlow,hup,hL] with X h₁ hU hX k hk hfit q r hq hr hc hqt z hz
  have hkp : 1≤k := (le_max_right ..).trans hk
  have ht : t₀≤(k:ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_left ..).trans hk))
  have hw := one_le_pow₀ (show 1≤1+log (log (X:ℝ)) by linarith only [log_nonneg (show 1≤log (X:ℝ) from hX)]) (n:=2)
  have hkL : (k:ℝ) ≤ log X := by
    nlinarith only [hfit,mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg (α:=ℝ) k),Nat.cast_nonneg (α:=ℝ) k]
  refine ⟨moment_from_hits (by positivity) (h₁ k ht hkL q r hq hr hc hqt z hz),?_⟩
  apply le_trans _ (hU k hkp hfit)
  unfold oneSidedMoment
  apply (sum_le_sum (g:=fun p => |(S p:ℝ)/p-log p/2|^k) (fun p _ => ?_)).trans
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ => pow_nonneg (abs_nonneg _) _))
  apply pow_le_pow_left₀ (le_max_left ..) (max_le (abs_nonneg _) _) _
  calc _ ≤ |z*((S p:ℝ)/p-log p/2)| := le_abs_self _
       _ = _ := by rw [abs_mul,hz,one_mul]

#print axioms matching
end
end Arxiv.«2501.03234».ThetaSharpSignedMoments
