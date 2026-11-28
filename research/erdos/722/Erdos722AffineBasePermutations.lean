import Erdos722AffineSignatureDual
import Erdos722VerticalAutomorphismGroup

/-! # Every automorphism of a separating quadruple system is affine -/

namespace Erdos722.QuadSwitch
open Finset Equiv Function Module
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}

abbrev affineCoords (hH : H.IsBlockDesign 3 4) (sep : Separates H) (o : V) : V ≃ labelSpace hH o :=
  signatureCoordinates hH sep o

private theorem four_zero {A : Type*} [AddCommGroup A] [Module (ZMod 2) A] (z : A) : 4 • z=0 := by
  have e : (4:ℕ) • z=(4:ZMod 2) • z := by rw [← Nat.cast_ofNat (R:=ZMod 2),Nat.cast_smul_eq_nsmul]
  rw [e,show (4:ZMod 2)=0 by decide,zero_smul]

omit [Fintype V] in
private theorem label_plane (hH : H.IsBlockDesign 3 4) (sep : Separates H) (o : V) {B : Finset V}
    (card : B.card=4) (zero : ∑ x∈B,label hH o x=0) : B∈H := by
  apply (affine_plane_test hH sep B).mpr
  refine ⟨card,?_⟩
  have h := congrArg (labelSpace hH o).subtype zero
  rw [map_sum,map_zero] at h
  change ∑ x∈B,(signature H x+signature H o)=0 at h
  rwa [sum_add_distrib,sum_const,card,four_zero,add_zero] at h

private def affinePerm (hH : H.IsBlockDesign 3 4) (sep : Separates H) (o : V)
    (L : labelSpace hH o ≃ₗ[ZMod 2] labelSpace hH o) (t : labelSpace hH o) : automorphisms H := by
  let C := affineCoords hH sep o
  let e := ((C.trans L.toEquiv).trans (Equiv.addRight t)).trans C.symm
  have key (x : V) : label hH o (e x)=L (label hH o x)+t := C.apply_symm_apply _
  refine ⟨e,eq_of_subset_of_card_le ?_ (by simp)⟩
  intro B hb
  obtain ⟨A,hA,rfl⟩ := mem_map.mp hb
  apply label_plane hH sep o (by simpa using hH.1 A hA)
  simp only [Equiv.finsetCongr_apply,sum_map,Function.Embedding.coeFn_mk,key]
  rw [sum_add_distrib,← map_sum,label_block_sum hH o hA,map_zero,zero_add,sum_const,hH.1 A hA,four_zero]

private theorem linear_part (hH : H.IsBlockDesign 3 4) (sep : Separates H) (o : V) (e : automorphisms H) :
    ∃ L : labelSpace hH o ≃ₗ[ZMod 2] labelSpace hH o, ∀ x,
      label hH o (e.val x)=L (label hH o x)+label hH o (e.val o) := by
  let C := affineCoords hH sep o
  let t := label hH o (e.val o)
  let T (z : labelSpace hH o) := C (e.val (C.symm z))+t
  let pull (u : Checks H) : Checks H :=
    ⟨u.val ∘ e.val,(check_relabel e.val H u.val).mp (e.prop.symm ▸ u.prop)⟩
  have coord (z : labelSpace hH o) (u : Checks H) : (T z).val u=z.val (pull u) := by
    obtain ⟨x,rfl⟩ := C.surjective z
    simp only [T,C.symm_apply_apply]
    change (u.val (e.val x)+u.val o)+(u.val (e.val o)+u.val o)=u.val (e.val x)+u.val (e.val o)
    rw [show ∀ a b c : ZMod 2, (a+b)+(c+b)=a+c by decide]
  let M : labelSpace hH o →ₗ[ZMod 2] labelSpace hH o :=
    { toFun := T, map_add' := by
        intro x y; apply Subtype.ext; funext u; change (T (x+y)).val u=(T x).val u+(T y).val u
        rw [coord (x+y) u,coord x u,coord y u]; rfl
      map_smul' := by
        intro k x; apply Subtype.ext; funext u; change (T (k • x)).val u=k • (T x).val u
        rw [coord (k • x) u,coord x u]; rfl }
  have inj : Injective M := fun x y h => C.symm.injective (e.val.injective (C.injective (add_right_cancel h)))
  let L := LinearEquiv.ofBijective M ((Finite.injective_iff_bijective).mp inj)
  refine ⟨L,fun x => ?_⟩
  change C (e.val x)=(C (e.val (C.symm (C x)))+t)+t
  rw [C.symm_apply_apply,add_assoc]
  have tt : t+t=0 := Subtype.ext (funext fun _ => CharTwo.add_self_eq_zero _)
  rw [tt,add_zero]

/-- A separating binary check model has the entire affine group, including all
translations. The equivalence here counts the unique linear and constant parts. -/
def affineBasePermutations (hH : H.IsBlockDesign 3 4) (sep : Separates H) (o : V) :
    ((labelSpace hH o ≃ₗ[ZMod 2] labelSpace hH o) × labelSpace hH o) ≃ automorphisms H := by
  let F (v : (labelSpace hH o ≃ₗ[ZMod 2] labelSpace hH o) × labelSpace hH o) := affinePerm hH sep o v.1 v.2
  let C := affineCoords hH sep o
  have key (L : labelSpace hH o ≃ₗ[ZMod 2] labelSpace hH o) (t : labelSpace hH o) (x : V) :
      C ((F (L,t)).val x)=L (C x)+t := C.apply_symm_apply _
  apply Equiv.ofBijective F
  constructor
  · rintro ⟨L,t⟩ ⟨M,u⟩ h
    have same (x : V) := congrArg (fun e : automorphisms H => C (e.val x)) h
    simp only [key] at same
    have tu : t=u := by simpa [show C o=0 from label_origin hH o] using same o
    subst u
    congr 1
    apply LinearEquiv.ext
    intro z; obtain ⟨x,rfl⟩ := C.surjective z
    exact add_right_cancel (same x)
  · intro e
    obtain ⟨L,h⟩ := linear_part hH sep o e
    exact ⟨⟨L,C (e.val o)⟩,Subtype.ext (Equiv.ext fun x => C.injective ((key _ _ x).trans (h x).symm))⟩

#print axioms affineCoords
#print axioms affineBasePermutations
end
end Erdos722.QuadSwitch
