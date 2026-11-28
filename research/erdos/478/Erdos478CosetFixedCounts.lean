import Erdos478FixedPointAverages
import Mathlib.Algebra.Group.Action.Prod
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

/-! # Fixed points averaged over a subgroup coset -/

namespace Erdos478.FrobeniusCounts
open Finset MulAction
open scoped Classical
noncomputable section
variable {G : Type*} [Group G]

private theorem fixed_sum (Y : Type*) [Fintype Y] [MulAction G Y] (g : G) :
    (fixedCount Y g : ℝ)=∑ y : Y, (if g • y=y then 1 else 0 : ℝ) := by
  classical
  rw [fixedCount,Nat.card_eq_fintype_card,Fintype.card_subtype,card_filter,Nat.cast_sum]
  apply sum_congr rfl
  intro y _
  by_cases h : g • y=y <;> simp [mem_fixedBy,h]

/-- If an element preserves each subgroup orbit setwise, averaging fixed
points over its coset gives the same mean as over the subgroup itself. -/
theorem twisted_fixed (N : Subgroup G) [Fintype N] (Y : Type*) [Fintype Y] [MulAction G Y]
    (g : G) (within : ∀ y : Y, ∃ n : N, n.val • y=g • y) :
    uniform N (fun n => (fixedCount Y (n.val*g) : ℝ))=uniform N (fun n => (fixedCount Y n.val : ℝ)) := by
  classical
  change (∑ n : N, (fixedCount Y (n.val*g) : ℝ))/_=(∑ n : N, (fixedCount Y n.val : ℝ))/_
  congr 1
  simp_rw [fixed_sum]
  rw [sum_comm]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro y _
  obtain ⟨a,ha⟩ := within y
  have eq := Equiv.sum_comp (Equiv.mulRight a) (fun n : N => (if n.val • y=y then 1 else 0 : ℝ))
  change (∑ n : N, (if (n.val*a.val) • y=y then 1 else 0 : ℝ))=_ at eq
  simpa only [mul_smul,ha] using eq

/-- Uniform group averages can be disintegrated by left multiplication
by a uniformly chosen subgroup element. -/
theorem coset_average [Fintype G] (N : Subgroup G) [Fintype N] (u : G → ℝ) :
    uniform G (fun g => uniform N (fun n => u (n.val*g)))=uniform G u := by
  change (∑ g : G, (∑ n : N, u (n.val*g)) / Fintype.card N) / _ = (∑ g : G, u g) / _
  congr 1
  rw [← sum_div,sum_comm]
  have translate (n : N) : (∑ g : G, u (n.val*g))=∑ g : G, u g := Equiv.sum_comp (Equiv.mulLeft n.val) u
  simp only [translate,sum_const,card_univ,nsmul_eq_mul]
  field_simp

/-- An observation constant on the chosen cosets can weight the average. -/
theorem weighted_coset [Fintype G] (N : Subgroup G) [Fintype N] (w u : G → ℝ) (c : ℝ)
    (hw : ∀ (n : N) g, w (n.val*g)=w g)
    (hc : ∀ g, uniform N (fun n => u (n.val*g))=c) :
    uniform G (fun g => w g*u g)=c*uniform G w := by
  rw [← coset_average N (fun g => w g*u g)]
  have eq (g : G) : uniform N (fun n => w (n.val*g)*u (n.val*g))=c*w g := by
    simp_rw [hw]
    change uniform N (w g • (fun n : N => u (n.val*g)))=_
    rw [map_smul,smul_eq_mul,hc,mul_comm]
  simp_rw [eq]
  exact (uniform G).map_smul c w

#print axioms twisted_fixed
#print axioms coset_average
#print axioms weighted_coset
end
end Erdos478.FrobeniusCounts
