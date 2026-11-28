import Erdos478CyclotomicCosetLabels
import Erdos478OccupiedProfileEnergy

/-! # Wilson's energy formula and a moving-set bound for consecutive coset profiles -/

namespace Erdos478.CyclotomicProfiles
open Finset
open scoped Classical
noncomputable section
variable {F : Type*} [Field F] [Fintype F]

theorem profile_energy (H : Subgroup Fˣ) (A : Finset F) (reg : ∀ x∈A, Regular x) :
    (equalPairs A (labelPair H)).card=A.card+(offCollisions A (multipliers H)).card := by
  let O := offCollisions A (multipliers H)
  have parts : equalPairs A (labelPair H)=A.diag∪O := by
    ext ⟨x,y⟩
    simp only [equalPairs,mem_filter,mem_product,mem_union,mem_diag,O,offCollisions,mem_offDiag]
    by_cases h : x=y
    · subst y
      simp
    · simp only [h,and_false,false_or,ne_eq,not_false_eq_true,and_true]
      constructor
      · rintro ⟨⟨hx,hy⟩,eq⟩
        exact ⟨⟨hx,hy⟩,(labelPair_eq (reg x hx) (reg y hy)).mp eq⟩
      · rintro ⟨⟨hx,hy⟩,eq⟩
        exact ⟨⟨hx,hy⟩,(labelPair_eq (reg x hx) (reg y hy)).mpr eq⟩
  have dis : Disjoint A.diag O := by
    apply disjoint_left.mpr
    intro xy he ho
    exact (mem_offDiag.mp (mem_filter.mp ho).1).2.2 (mem_diag.mp he).2
  rw [parts,card_union_of_disjoint dis,diag_card]

theorem profile_occupation (H : Subgroup Fˣ) (A : Finset F) (reg : ∀ x∈A, Regular x) :
    A.card^2 ≤ (A.image (labelPair H)).card*(A.card+(Nat.card H-1)*(Nat.card H-2)) := by
  have one : (1:F)∈multipliers H := (multiplier_mem (1:Fˣ)).mpr H.one_mem
  have bound := off_collision_bound reg one
  rw [multipliers_card] at bound
  have cs := support_energy A (labelPair H)
  rw [profile_energy H A reg] at cs
  apply cs.trans
  exact Nat.mul_le_mul_left (A.image (labelPair H)).card (Nat.add_le_add_left bound A.card)

theorem complete_profile_energy (H : Subgroup Fˣ) :
    let A := univ.filter (Regular (F:=F))
    (equalPairs A (labelPair H)).card=A.card+(Nat.card H-1)*(Nat.card H-2) := by
  dsimp only
  rw [profile_energy H _ (fun _ h => (mem_filter.mp h).2)]
  have nz : (0:F)∉multipliers H := by
    intro h
    obtain ⟨u,_,eq⟩ := mem_image.mp h
    exact u.val.ne_zero eq
  have one : (1:F)∈multipliers H := (multiplier_mem (1:Fˣ)).mpr H.one_mem
  rw [off_collision_exact _ one nz,multipliers_card]

#print axioms profile_energy
#print axioms profile_occupation
#print axioms complete_profile_energy
end
end Erdos478.CyclotomicProfiles
