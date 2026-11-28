import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.SetTheory.Cardinal.Finite

/-! # Products of fixed-point counts under the uniform group average -/

namespace Erdos478.FrobeniusCounts
open Finset MulAction
noncomputable section

/-- Uniform average on a finite type. -/
def uniform (G : Type*) [Fintype G] : (G → ℝ) →ₗ[ℝ] ℝ where
  toFun w := (∑ g, w g) / Fintype.card G
  map_add' w v := by simp [sum_add_distrib,add_div]
  map_smul' c w := by
    change (∑ g, c*w g)/_ = c*((∑ g, w g)/_)
    rw [← mul_sum,mul_div_assoc]

theorem uniform_nonneg {G : Type*} [Fintype G] {w : G → ℝ} (h : ∀ g, 0≤w g) :
    0≤uniform G w := div_nonneg (sum_nonneg (fun g _ => h g)) (Nat.cast_nonneg _)

theorem uniform_one (G : Type*) [Fintype G] [Nonempty G] : uniform G (fun _ => 1)=1 := by
  simp [uniform,Fintype.card_ne_zero]

def fixedCount {G : Type*} [Group G] (Y : Type*) [MulAction G Y] (g : G) : ℕ :=
  Nat.card (fixedBy Y g)

private def fixedPi {G I : Type*} [Group G] (Y : I → Type*) [∀ i, MulAction G (Y i)] (g : G) :
    fixedBy ((i : I) → Y i) g ≃ ((i : I) → fixedBy (Y i) g) where
  toFun v i := ⟨v.val i,congrFun (mem_fixedBy.mp v.prop) i⟩
  invFun z := ⟨fun i => (z i).val,funext fun i => (z i).prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem fixed_pi {G I : Type*} [Group G] [Fintype I] (Y : I → Type*) [∀ i, MulAction G (Y i)]
    (g : G) : fixedCount ((i : I) → Y i) g=∏ i, fixedCount (Y i) g := by
  rw [fixedCount,Nat.card_congr (fixedPi Y g),Nat.card_pi]
  rfl

/-- Burnside's lemma, with an arbitrary finite set of root coordinates.
Repeated coordinates correspond to higher moments. -/
theorem uniform_product_fixed {G I : Type*} [Group G] [Fintype G] [Fintype I]
    (Y : I → Type*) [∀ i, Fintype (Y i)] [∀ i, MulAction G (Y i)] :
    uniform G (fun g => ∏ i, (fixedCount (Y i) g : ℝ)) =
      (Nat.card (orbitRel.Quotient G ((i : I) → Y i)) : ℝ) := by
  classical
  let W := (i : I) → Y i
  let Ω := orbitRel.Quotient G W
  let : Fintype Ω := Fintype.ofFinite Ω
  let (g : G) : Fintype (fixedBy W g) := Fintype.ofFinite _
  have sum := sum_card_fixedBy_eq_card_orbits_mul_card_group G W
  change (∑ g, ∏ i, (fixedCount (Y i) g : ℝ)) / Fintype.card G=(Nat.card Ω : ℝ)
  apply (div_eq_iff (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero : Fintype.card G ≠ 0))).mpr
  simp_rw [← Nat.cast_prod,← fixed_pi Y]
  rw [← Nat.cast_sum,← Nat.cast_mul]
  exact_mod_cast (by simpa only [fixedCount,Nat.card_eq_fintype_card] using sum :
    (∑ g : G, fixedCount W g)=Nat.card Ω*Fintype.card G)

#print axioms uniform
#print axioms uniform_nonneg
#print axioms uniform_one
#print axioms fixedCount
#print axioms fixed_pi
#print axioms uniform_product_fixed
end
end Erdos478.FrobeniusCounts
