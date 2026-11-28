import Erdos722CyclotomicCosets

/-!
# Representatives up to sign

In an even-order subgroup of an odd finite field, each pair of opposite
multipliers contributes one representative.
-/

namespace Erdos722.Cyclotomy
open Finset
open scoped Classical
variable {F : Type*} [Field F] [Fintype F]

theorem half_multipliers (H : Subgroup Fˣ) (hneg : (-1:Fˣ)∈H) (hchar : (-1:F)≠1) :
    ∃ R : Finset Fˣ, 2*R.card = Nat.card H ∧ ∀ u ∈ H, u∈R ∨ -u∈R := by
  classical
  let order := Fintype.equivFin Fˣ
  let U := (H : Set Fˣ).toFinset
  let R := U.filter fun u => order u < order (-u)
  let negEmb : Fˣ ↪ Fˣ := ⟨Neg.neg,neg_injective⟩
  have fixed (u : Fˣ) : u ≠ -u := by
    intro e
    apply hchar
    apply mul_right_cancel₀ (b := (u:F)) u.ne_zero
    simpa using congrArg Units.val e.symm
  have neg_mem (u : Fˣ) (h : u∈H) : -u∈H := by simpa using H.mul_mem hneg h
  have covers (u : Fˣ) (h : u∈H) : u∈R ∨ -u∈R := by
    rcases lt_or_gt_of_ne (order.injective.ne (fixed u)) with lt|gt
    · exact Or.inl (mem_filter.mpr ⟨by simpa [U] using h,lt⟩)
    · exact Or.inr (mem_filter.mpr ⟨by simpa [U] using neg_mem u h,by simpa using gt⟩)
  have disj : Disjoint R (R.map negEmb) := by
    apply disjoint_left.mpr
    intro u hu hn
    obtain ⟨v,hv,rfl⟩ := mem_map.mp hn
    have h₁ := (mem_filter.mp hv).2
    have h₂ := (mem_filter.mp hu).2
    change order (-v) < order (- -v) at h₂
    rw [neg_neg] at h₂
    exact (not_lt_of_gt h₁) h₂
  have cover : R ∪ R.map negEmb = U := by
    ext u
    constructor
    · intro h
      rcases mem_union.mp h with h|h
      · exact (mem_filter.mp h).1
      · obtain ⟨v,hv,rfl⟩ := mem_map.mp h
        have hh : v∈H := by simpa [U] using (mem_filter.mp hv).1
        simpa [negEmb,U] using neg_mem v hh
    · intro hu
      rcases covers u (by simpa [U] using hu) with h|h
      · exact mem_union_left _ h
      · exact mem_union_right _ (mem_map.mpr ⟨-u,h,by simp [negEmb]⟩)
  refine ⟨R,?_,covers⟩
  calc
    _ = (R ∪ R.map negEmb).card := by rw [card_union_of_disjoint disj,card_map]; omega
    _ = _ := by rw [cover]; simp [U,Nat.card_eq_fintype_card]

#print axioms half_multipliers

end Erdos722.Cyclotomy
