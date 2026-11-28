import Erdos722CosetTranslationKernel
import Erdos722TranslationsBetweenFillings
import Erdos722MarkedPointGroup

/-! # Unrestricted point isomorphisms of the coset-filled Steiner quadruple systems -/

namespace Erdos722.FourPoint
open Finset QuadCompletion QuadSwitch Equiv
noncomputable section
attribute [local instance] cubeOrder cubeDec

abbrev cosetRule (d : ℕ) (hd : 6≤d) (c : CosetPattern d) (u : CubeOffsets (d+2)) :=
  colouredRule (cubeRule (d+2)) (markedMatching (d+2) (by omega)) (cosetColours d hd c) u

def cosetDesign (d : ℕ) (hd : 6≤d) (c : CosetPattern d) (u : CubeOffsets (d+2)) :=
  labelledBlocks (d+2) (cosetRule d hd c u)

/-- The design is on the canonical finite point set, with corank d+3. -/
theorem coset_design_rank (d : ℕ) (hd : 6≤d) (c : CosetPattern d) (u : CubeOffsets (d+2)) :
    (cosetDesign d hd c u).IsBlockDesign 3 4 ∧
      (binaryIncidence (cosetDesign d hd c u)).rank+(d+3)=4*2^(d+2) :=
  arbitrary_filling_rank (d+2) (rigidWord_top _ (by omega)) _ (blockwise_compatible ..)

theorem coset_iso_iff (d : ℕ) (hd : 6≤d) (c f : CosetPattern d) (u v : CubeOffsets (d+2))
    (e : Perm (Cube (d+2) × Fibre)) :
    e.finsetCongr.finsetCongr (cosetRule d hd c u).blocks=(cosetRule d hd f v).blocks ↔
      c=f ∧ ∃ t : Cube (d+2) → Fibre, v=u+cosetGradient d hd c t ∧ e=pointForm 1 1 t := by
  let Q := cubeRule (d+2)
  let M := markedMatching (d+2) (by omega)
  have hw := rigidWord_top (d+2) (by omega)
  have hyp : FibreHypotheses Q M :=
    ⟨cube_separates _,⟨0,edge_normalized 0 _⟩,(noFix_edge_iff ..).mpr hw⟩
  have size : 3≤Fintype.card (Cube (d+2)) := by
    simpa [Cube] using (show 3≤2^(d+2) by have := sparse_basis_size (by omega : 6≤d+2); omega)
  constructor
  · intro eq
    have plain (b : Perm (Cube (d+2))) : ∃ o, PlainThrough (cosetRule d hd c u) o ∧
        PlainThrough (cosetRule d hd f v) (b o) := by
      obtain ⟨o,src,dst⟩ := coset_common_anchor d hd b
      exact ⟨o,coset_plain d hd c M u src,coset_plain d hd f M v dst⟩
    obtain ⟨t,rfl⟩ := translation_between_fillings (blockwise_compatible ..) (blockwise_compatible ..)
      hyp size (path_word_frames (d+2) (by omega)) plain e eq
    have same := (translation_coloured_blocks M (cosetColours d hd c) u t).symm.trans eq
    have ident := coset_colours_recovered d hd c f M _ v same
    subst f
    exact ⟨rfl,t,(translation_coloured_iff M _ u v t).mp eq,rfl⟩
  · rintro ⟨rfl,t,offset,rfl⟩
    exact (translation_coloured_iff M _ u v t).mpr offset

theorem coset_class_iff (d : ℕ) (hd : 6≤d) (c f : CosetPattern d) (u v : CubeOffsets (d+2)) :
    classOf (cosetDesign d hd c u)=classOf (cosetDesign d hd f v) ↔
      c=f ∧ ∃ t : Cube (d+2) → Fibre, v=u+cosetGradient d hd c t := by
  rw [class_eq_iff,cosetDesign,cosetDesign,labelledBlocks,labelledBlocks,relabel_iso_iff]
  constructor
  · rintro ⟨e,he⟩
    obtain ⟨eq,t,h,_⟩ := (coset_iso_iff d hd c f u v e).mp he
    exact ⟨eq,t,h⟩
  · rintro ⟨eq,t,h⟩
    exact ⟨_,(coset_iso_iff d hd c f u v _).mpr ⟨eq,t,h,rfl⟩⟩

theorem coset_asymmetric (d : ℕ) (hd : 6≤d) (c : CosetPattern d) (u : CubeOffsets (d+2))
    (e : automorphisms (cosetDesign d hd c u)) : e=1 := by
  let R := cosetRule d hd c u
  let L := automorphismRelabel (fourLabels (d+2)) R.blocks
  obtain ⟨a,rfl⟩ := L.surjective e
  obtain ⟨_,t,fix,form⟩ := (coset_iso_iff d hd c c u u a.val).mp a.prop
  have z := coset_kernel_zero d hd c t (add_left_cancel (a:=u) (fix.symm.trans (add_zero u).symm))
  have one : a=1 := by
    apply Subtype.ext
    apply Equiv.ext
    rintro ⟨i,x⟩
    change a.val (i,x)=(i,x)
    rw [form,z]
    change (i,move 1 x+0)=(i,x)
    rw [move_one,add_zero]
  change L a=1
  rw [one,map_one]

#print axioms cosetRule
#print axioms cosetDesign
#print axioms coset_design_rank
#print axioms coset_iso_iff
#print axioms coset_class_iff
#print axioms coset_asymmetric
end
end Erdos722.FourPoint
