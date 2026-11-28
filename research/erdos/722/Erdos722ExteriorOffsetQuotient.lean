import Erdos722SparseMarkedLayouts
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # One exterior offset per orbit of the independent fibre translations -/

namespace Erdos722.AffineStar
open Finset QuadCompletion FourPoint QuadSwitch LatinFillings
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec
variable {d : ℕ} {hd : 6≤d}

abbrev ExteriorOffsets (L : Layout d hd) := L.exterior → Fibre

def measurements (L : Layout d hd) : (Base d → Fibre) →+ ExteriorOffsets L where
  toFun t B := weightedGradient (cubeRule (d+2)) (colours d hd) t ⟨B.val,L.sub B.prop⟩
  map_zero' := funext fun B => congrFun (map_zero (weightedGradient _ _)) ⟨B.val,L.sub B.prop⟩
  map_add' t s := funext fun B => congrFun (map_add (weightedGradient _ _) t s) ⟨B.val,L.sub B.prop⟩

theorem measurements_injective (L : Layout d hd) : Function.Injective (measurements L) := by
  intro t u eq
  apply sub_eq_zero.mp
  apply L.detects
  intro B h
  have z : measurements L (t-u)=0 := by rw [map_sub,eq,sub_self]
  exact congrFun z ⟨B.val,h⟩

abbrev OffsetClass (L : Layout d hd) := ExteriorOffsets L ⧸ (measurements L).range

/-- A translation taking two chosen representatives to one another is the identity. -/
theorem offset_rigidity (L : Layout d hd) (a b : OffsetClass L) (t : Base d → Fibre)
    (eq : b.out=a.out+measurements L t) : a=b ∧ t=0 := by
  have same : b=a := calc
    b = QuotientAddGroup.mk b.out := (QuotientAddGroup.out_eq' b).symm
    _ = QuotientAddGroup.mk a.out := by
      rw [eq]
      exact QuotientAddGroup.mk_add_of_mem _ (show measurements L t∈(measurements L).range from ⟨t,rfl⟩)
    _ = a := QuotientAddGroup.out_eq' a
  subst b
  refine ⟨rfl,measurements_injective L ?_⟩
  rw [map_zero]
  exact add_left_cancel ((eq.symm).trans (add_zero a.out).symm)

/-- The offset contribution after dividing by all 4^n fibre translations. -/
theorem offset_class_count (L : Layout d hd) : Nat.card (OffsetClass L)=4^(L.exterior.card-2^(d+2)) := by
  have ambient : Nat.card (ExteriorOffsets L)=4^L.exterior.card := by
    simp [ExteriorOffsets,Nat.card_eq_fintype_card,Fibre]
  have source : Nat.card (Base d → Fibre)=4^(2^(d+2)) := by simp [Base,Cube,Fibre,Nat.card_eq_fintype_card]
  have range : Nat.card (measurements L).range=4^(2^(d+2)) :=
    (Nat.card_congr (AddMonoidHom.ofInjective (measurements_injective L)).toEquiv).symm.trans source
  have le := Nat.card_le_card_of_injective _ (measurements_injective L)
  rw [ambient,source] at le
  have ex := (Nat.pow_le_pow_iff_right (by decide : 1<4)).mp le
  have count := (measurements L).range.card_eq_card_quotient_mul_card_addSubgroup
  rw [ambient,range] at count
  apply Nat.eq_of_mul_eq_mul_right (by positivity : 0<4^(2^(d+2)))
  rwa [← pow_add,Nat.sub_add_cancel ex,eq_comm]

def outerOffset (L : Layout d hd) (a : OffsetClass L) : BlockOffsets (cubeRule (d+2)) :=
  fun B => if h : B.val∈L.exterior then a.out ⟨B.val,h⟩ else 0

#print axioms ExteriorOffsets
#print axioms measurements
#print axioms measurements_injective
#print axioms OffsetClass
#print axioms offset_rigidity
#print axioms offset_class_count
#print axioms outerOffset
end
end Erdos722.AffineStar
