import ThetaCenterBounds

/-! Excursions of the original prime theta sum on both sides of its leading term. -/
namespace Arxiv.«2501.03234».ThetaHalfLogExcursions
open Finset Filter Real ThetaReciprocalBlocks ThetaOffDiagonalSigns ThetaPrimeDensity
open ThetaDivisibleDiagonal ThetaDiagonalConstant ThetaCenterBounds

private lemma common_factor_mass {V : ℕ} (hV : 2≤V) :
    121/100≤commonWeight (2*V^52) 3 := by
  have hu : 21≤2*V^52/3 := by have := Nat.pow_le_pow_left hV 52; omega
  let s := (range 22).filter (fun g => g%2=1)
  have hs : s⊆(Icc 1 (2*V^52/3)).filter (fun g => g%2=1) := by
    intro g hg
    obtain ⟨hgo,ho⟩ := mem_filter.mp hg
    have h := mem_range.mp hgo
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,ho⟩
  have hq : (121/100:ℚ)<∑ g∈(range 22).filter (fun g => g%2=1),((g:ℚ)^2)⁻¹ := by decide +kernel
  have h := (Rat.cast_lt (K:=ℝ)).mpr hq
  push_cast at h
  exact h.le.trans (sum_le_sum_of_subset_of_nonneg hs (fun g _ _ => by positivity))

/-- The signed residual from the leading term has opposite linear
excursions on sets of positive upper density relative to all primes. -/
theorem S_half_log_excursions :
    PositiveUpperPrimeDensity (fun p => p%24=1 ∧ (p:ℝ)*log p/2+13*(p:ℝ)/50<(S p:ℝ)) ∧
    PositiveUpperPrimeDensity (fun p => p%24=17 ∧ (S p:ℝ)<(p:ℝ)*log p/2-(p:ℝ)/1000) := by
  have hc : (13/50:ℝ)<32*(121/100)/(15*π^2) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith only [mul_self_lt_mul_self pi_pos.le pi_lt_d4]
  obtain ⟨H₁,H₂⟩ := S_prime_excursion_densities_of_weight (fun _ => common_factor_mass) hc
  constructor
  · apply PositiveUpperPrimeDensity.of_eventually_imp _ H₁
    filter_upwards [diagonal_second_order.eventually_const_lt center_bounds.1,eventually_ge_atTop 1] with p hp hp' h
    have hlt : log p/2*(p:ℝ)<divisibleDiagonal p :=
      (lt_div_iff₀ (by exact_mod_cast hp')).mp (by linarith only [hp])
    exact ⟨h.1,by linarith only [h.2,hlt]⟩
  · apply PositiveUpperPrimeDensity.of_eventually_imp _ H₂
    filter_upwards [diagonal_second_order.eventually_lt_const center_bounds.2,eventually_ge_atTop 1] with p hp hp' h
    have hlt : divisibleDiagonal p<(log p/2+259/1000)*(p:ℝ) :=
      (div_lt_iff₀ (by exact_mod_cast hp')).mp (by linarith only [hp])
    exact ⟨h.1,by linarith only [h.2,hlt]⟩

end Arxiv.«2501.03234».ThetaHalfLogExcursions
#print axioms Arxiv.«2501.03234».ThetaHalfLogExcursions.S_half_log_excursions
