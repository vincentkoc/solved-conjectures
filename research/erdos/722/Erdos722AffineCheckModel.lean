import Erdos722BinaryCheckBases

/-! # Intrinsic affine coordinates for any separating Steiner quadruple system -/

namespace Erdos722.QuadSwitch
open Finset Function
noncomputable section
variable {V : Type*} [DecidableEq V] {H : Finset (Finset V)}

def signature (H : Finset (Finset V)) (x : V) : Checks H → ZMod 2 := fun u => u.val x

omit [DecidableEq V] in
theorem signature_injective (sep : Separates H) : Injective (signature H) :=
  fun x y eq => sep x y fun u hu => congrFun eq ⟨u,hu⟩

omit [DecidableEq V] in
theorem signature_sum {B : Finset V} (hb : B∈H) : (∑ x∈B,signature H x)=0 := by
  funext f
  rw [Finset.sum_apply]
  exact f.prop B hb

/-- The intrinsic check coordinates detect exactly the affine planes in the point set. -/
theorem affine_plane_test (hH : H.IsBlockDesign 3 4) (sep : Separates H) (B : Finset V) :
    B∈H ↔ B.card=4 ∧ (∑ x∈B,signature H x)=0 := by
  refine ⟨fun hb => ⟨hH.1 B hb,signature_sum hb⟩,?_⟩
  rintro ⟨hB,zero⟩
  obtain ⟨T,sub,ht⟩ := exists_subset_card_eq (s:=B) (n:=3) (by omega)
  obtain ⟨C,⟨hc,tc⟩,_⟩ := hH.2 T ht
  obtain ⟨x,hx,rfl⟩ := exists_eq_insert_iff.mpr ⟨sub,by omega⟩
  obtain ⟨y,hy,cy⟩ := exists_eq_insert_iff.mpr ⟨tc,by rw [hH.1 C hc,ht]⟩
  have csum := signature_sum hc
  rw [← cy,sum_insert hy] at csum
  rw [sum_insert hx] at zero
  have eq := signature_injective sep (add_right_cancel (zero.trans csum.symm))
  rw [eq,cy]; exact hc

private theorem twice {I : Type*} (f : I → ZMod 2) : f+f=0 := funext fun i => CharTwo.add_self_eq_zero (f i)

/-- The check vectors of the points are closed under ternary addition. -/
theorem signature_ternary (hH : H.IsBlockDesign 3 4) (x y z : V) :
    ∃ w, signature H w=signature H x+signature H y+signature H z := by
  classical
  by_cases xy : x=y
  · subst y; exact ⟨z,by rw [twice,zero_add]⟩
  by_cases yz : y=z
  · subst z; exact ⟨x,by rw [add_assoc,twice,add_zero]⟩
  by_cases xz : x=z
  · subst z; exact ⟨y,by rw [add_right_comm,twice,zero_add]⟩
  let T : Finset V := {x,y,z}
  have ht : T.card=3 := by simp [T,xy,xz,yz]
  obtain ⟨B,⟨hb,sub⟩,_⟩ := hH.2 T ht
  obtain ⟨w,hw,bw⟩ := exists_eq_insert_iff.mpr ⟨sub,by rw [hH.1 B hb,ht]⟩
  have zero := signature_sum hb
  rw [← bw,sum_insert hw] at zero
  have eq : signature H w=∑ a∈T,signature H a := add_right_cancel (zero.trans (twice _).symm)
  exact ⟨w,by simpa [T,xy,xz,yz,add_assoc] using eq⟩

def signatureSpace (hH : H.IsBlockDesign 3 4) (a : V) : AddSubgroup (Checks H → ZMod 2) where
  carrier := {u | ∃ x, signature H x+signature H a=u}
  zero_mem' := ⟨a,twice _⟩
  add_mem' := by
    rintro _ _ ⟨x,rfl⟩ ⟨y,rfl⟩
    obtain ⟨z,hz⟩ := signature_ternary hH x y a
    exact ⟨z,by rw [hz]; abel⟩
  neg_mem' := by
    rintro _ ⟨x,rfl⟩
    exact ⟨x,(eq_neg_of_add_eq_zero_left (twice _))⟩

/-- Translate by a base point to identify the whole point set bijectively with
an additive subgroup of a binary vector space. -/
def signatureCoordinates (hH : H.IsBlockDesign 3 4) (sep : Separates H) (a : V) : V ≃ signatureSpace hH a :=
  Equiv.ofBijective (fun x => ⟨signature H x+signature H a,x,rfl⟩)
    ⟨fun _ _ eq => signature_injective sep (add_right_cancel (congrArg Subtype.val eq)),
      fun ⟨_,x,hx⟩ => ⟨x,Subtype.ext hx⟩⟩

#print axioms signature
#print axioms signature_injective
#print axioms signature_sum
#print axioms affine_plane_test
#print axioms signature_ternary
#print axioms signatureSpace
#print axioms signatureCoordinates
end
end Erdos722.QuadSwitch
