import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Prime logarithmic weights in proportional intervals

The discrepancy between a selected von Mangoldt sum and its prime part
is at most the full contribution of proper prime powers. This bound
is uniform in the chosen set of integers.
-/

namespace Erdos478.BandWeights
open Finset Filter ArithmeticFunction
open scoped Topology Classical
noncomputable section

def mass (P : ℕ → Prop) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, if P n then vonMangoldt n else 0

def primeWeight (P : ℕ → Prop) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, if P n ∧ n.Prime then Real.log n else 0

def countingInput (P : ℕ → Prop) (c : ℝ) :=
  Tendsto (fun N : ℕ => mass P N/N) atTop (𝓝 c)

theorem error_bounds (P : ℕ → Prop) (N : ℕ) :
    0≤mass P N-primeWeight P N ∧ mass P N-primeWeight P N≤Chebyshev.psi N-Chebyshev.theta N := by
  rw [mass,primeWeight,← sum_sub_distrib,Chebyshev.psi_sub_theta_eq_sum_not_prime]
  simp only [Nat.floor_natCast,sum_filter]
  constructor
  · apply sum_nonneg
    intro n _
    by_cases h : n.Prime <;> by_cases hp : P n <;> simp [h,hp,vonMangoldt_apply_prime]
  · apply sum_le_sum
    intro n _
    by_cases h : n.Prime <;> by_cases hp : P n <;> simp [h,hp,vonMangoldt_apply_prime]

theorem prime_weight_limit {P : ℕ → Prop} {c : ℝ} (h : countingInput P c) :
    Tendsto (fun N : ℕ => primeWeight P N/N) atTop (𝓝 c) := by
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have err : Tendsto (fun N : ℕ => (mass P N-primeWeight P N)/N) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      ((Real.tendsto_sqrt_atTop.comp hn).const_div_atTop C)
    · exact Eventually.of_forall fun n => div_nonneg (error_bounds P n).1 (Nat.cast_nonneg _)
    · filter_upwards [eventually_gt_atTop 0] with n hp
      have hp' : 0<(n:ℝ) := by exact_mod_cast hp
      have hs := Real.sqrt_pos.mpr hp'
      apply (div_le_div_iff₀ hp' hs).mpr
      have bound := mul_le_mul_of_nonneg_right ((error_bounds P n).2.trans (hC n)) hs.le
      rwa [mul_assoc,Real.mul_self_sqrt hp'.le] at bound
  have lim := h.sub err
  rw [sub_zero] at lim
  apply lim.congr'
  exact Eventually.of_forall fun n => by dsimp; ring

#print axioms error_bounds
#print axioms prime_weight_limit
end
end Erdos478.BandWeights
