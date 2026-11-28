import Erdos722AffineCheckModel
import Erdos722QuadSwitchClassification

/-! # Parity of projected blocks forces a compatible two-point lift -/

namespace Erdos722.QuadSwitch
open Finset Function
noncomputable section
variable {V : Type*} [DecidableEq V] {H : Finset (Finset V)}

private theorem double_zero {I : Type*} (f : I → ZMod 2) : f+f=0 := funext fun i => CharTwo.add_self_eq_zero (f i)

/-- A four-set with zero projected signature is either a pair of full fibres
or projects bijectively onto a base block. -/
theorem projection_block (hH : H.IsBlockDesign 3 4) (sep : Separates H) (D : Finset (V × Bool))
    (card : D.card=4) (zero : ∑ x∈D,signature H x.1=0) :
    (∃ P : Finset V, P.card=2 ∧ twins P=D) ∨ footprint D∈H := by
  classical
  by_cases inj : Set.InjOn Prod.fst (D : Set (V × Bool))
  · right
    apply (affine_plane_test hH sep _).mpr
    exact ⟨(card_image_of_injOn inj).trans card,(sum_image inj).trans zero⟩
  left
  simp only [Set.InjOn] at inj
  push Not at inj
  obtain ⟨x,hx,y,hy,xy,ne⟩ := inj
  let R := (D.erase x).erase y
  have ry : y∈D.erase x := mem_erase.mpr ⟨ne.symm,hy⟩
  have rc : R.card=2 := by dsimp [R]; rw [card_erase_of_mem ry,card_erase_of_mem hx,card]
  obtain ⟨s,t,st,pair⟩ := card_eq_two.mp rc
  have de : D=insert x (insert y R) := by dsimp [R]; rw [insert_erase ry,insert_erase hx]
  have nx : x∉insert y R := by simp [R,ne]
  have ny : y∉R := notMem_erase _ _
  rw [de,sum_insert nx,sum_insert ny,pair,sum_pair st,← xy,← add_assoc,double_zero,zero_add] at zero
  have sig : signature H s.1=signature H t.1 := add_right_cancel (zero.trans (double_zero _).symm)
  have same := signature_injective sep sig
  let P : Finset V := {x.1,s.1}
  have sub : D⊆twins P := by
    intro a ha
    rw [de,pair] at ha
    simp only [mem_insert,mem_singleton] at ha
    rcases ha with rfl|rfl|rfl|rfl <;> apply mem_product.mpr <;> simp [P,xy,same]
  have le := card_le_card sub
  rw [card,twins_card] at le
  have pc : P.card=2 := by have up : P.card≤2 := card_le_two; omega
  refine ⟨P,pc,(eq_of_subset_of_card_le sub ?_).symm⟩
  rw [twins_card,pc,card]

theorem compatible_of_projected_sums (hH : H.IsBlockDesign 3 4) (sep : Separates H)
    {D : Finset (Finset (V × Bool))} (hD : D.IsBlockDesign 3 4)
    (zero : ∀ B∈D, ∑ x∈B,signature H x.1=0) : Compatible H D :=
  fun B hb => projection_block hH sep B (hD.1 B hb) (zero B hb)

#print axioms projection_block
#print axioms compatible_of_projected_sums
end
end Erdos722.QuadSwitch
