import Erdos478PairCosetMoments
import Mathlib.Tactic.Linarith

/-! # Weighted hit probabilities after conditioning on a subgroup coset -/

namespace Erdos478.FrobeniusCounts
open Finset MulAction
open scoped Classical
noncomputable section

theorem uniform_mono {G : Type*} [Fintype G] {a b : G → ℝ} (h : ∀ g, a g≤b g) :
    uniform G a≤uniform G b := div_le_div_of_nonneg_right
      (sum_le_sum (fun g _ => h g)) (Nat.cast_nonneg _)

variable {G Y : Type*} [Group G] [Fintype G] [Fintype Y] [Nontrivial Y] [MulAction G Y]
variable (N : Subgroup G) [Fintype N]
variable (pairs : ∀ a b c d : Y, (a=b ↔ c=d) → ∃ n : N, n.val • a=c ∧ n.val • b=d)
variable (w : G → ℝ) (stable : ∀ (n : N) g, w (n.val*g)=w g)

include pairs stable

theorem conditional_moments :
    uniform G (fun g => w g*(fixedCount Y g : ℝ))=uniform G w ∧
    uniform G (fun g => w g*(fixedCount Y g : ℝ)^2)=2*uniform G w := by
  constructor
  · simpa only [one_mul] using weighted_coset N w (fun g => (fixedCount Y g : ℝ)) 1 stable
      (fun g => (pair_coset_moments N pairs g).1)
  · exact weighted_coset N w (fun g => (fixedCount Y g : ℝ)^2) 2 stable
      (fun g => (pair_coset_moments N pairs g).2)

/-- A nonnegative observation constant on the cosets retains at least
half its total mass when a fixed point is required. -/
theorem conditional_half (nonneg : ∀ g, 0≤w g) :
    uniform G w≤2*uniform G (fun g => if 0<fixedCount Y g then w g else 0) := by
  let a (g : G) : ℝ := w g*(fixedCount Y g : ℝ)
  let b (g : G) : ℝ := w g*(fixedCount Y g : ℝ)^2
  let h (g : G) : ℝ := if 0<fixedCount Y g then w g else 0
  have le (g : G) : ((4:ℝ) • a-b) g≤((4:ℝ) • h) g := by
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,a,b,h]
    split_ifs with pos
    · nlinarith [mul_nonneg (nonneg g) (sq_nonneg ((fixedCount Y g : ℝ)-2))]
    · simp [show fixedCount Y g=0 by omega]
  have L := uniform_mono le
  obtain ⟨one,two⟩ := conditional_moments N pairs w stable
  change uniform G a=uniform G w at one
  change uniform G b=2*uniform G w at two
  rw [map_sub,map_smul,map_smul,smul_eq_mul,smul_eq_mul,one,two] at L
  change uniform G w≤2*uniform G h
  linarith

#print axioms uniform_mono
#print axioms conditional_moments
#print axioms conditional_half
end
end Erdos478.FrobeniusCounts
