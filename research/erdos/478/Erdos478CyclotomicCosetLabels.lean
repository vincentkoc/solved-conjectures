import Erdos478CyclotomicOffDiagonal
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Profiles of successive arguments in the quotient by a multiplicative subgroup -/

namespace Erdos478.CyclotomicProfiles
open Finset
open scoped Classical
noncomputable section
variable {F : Type*} [Field F] [Fintype F]

def multipliers (H : Subgroup Fˣ) : Finset F := (univ : Finset H).image (fun h => (h.val : F))
theorem multiplier_mem {H : Subgroup Fˣ} (u : Fˣ) : (u:F) ∈ multipliers H ↔ u∈H := by
  constructor
  · intro h
    obtain ⟨s,_,eq⟩ := mem_image.mp h
    exact (Units.ext eq : s.val=u) ▸ s.prop
  · intro h
    exact mem_image.mpr ⟨⟨u,h⟩,mem_univ _,rfl⟩

theorem multipliers_card (H : Subgroup Fˣ) : (multipliers H).card=Nat.card H := by
  rw [multipliers,card_image_of_injective _ (fun x y h => Subtype.ext (Units.ext h)),card_univ,Nat.card_eq_fintype_card]

def label (H : Subgroup Fˣ) (x : F) : Fˣ ⧸ H :=
  if hx : x=0 then 1 else QuotientGroup.mk (Units.mk0 x hx)

theorem labels_eq {H : Subgroup Fˣ} {x y : F} (hx : x≠0) (hy : y≠0) :
    label H x=label H y ↔ x/y∈multipliers H := by
  let a := Units.mk0 x hx
  let b := Units.mk0 y hy
  rw [label,label,dif_neg hx,dif_neg hy,eq_comm,QuotientGroup.eq]
  have eq : ((b⁻¹*a:Fˣ):F)=x/y := by simp [a,b,div_eq_mul_inv,mul_comm]
  exact (multiplier_mem (H:=H) (b⁻¹*a)).symm.trans (eq ▸ Iff.rfl)

def labelPair (H : Subgroup Fˣ) (x : F) := (label H x,label H (x+1))

theorem labelPair_eq {H : Subgroup Fˣ} {x y : F} (hx : Regular x) (hy : Regular y) :
    labelPair H x=labelPair H y ↔
    (profileRatios x y).1∈multipliers H ∧ (profileRatios x y).2∈multipliers H :=
  Prod.mk.injEq .. |>.to_iff |>.trans (and_congr (labels_eq hx.1 hy.1) (labels_eq hx.2 hy.2))

#print axioms multipliers
#print axioms multiplier_mem
#print axioms multipliers_card
#print axioms label
#print axioms labels_eq
#print axioms labelPair
#print axioms labelPair_eq
end
end Erdos478.CyclotomicProfiles
