import Erdos722SparseMarkedIsomorphisms

/-! # The full point group of a marked quadruple system at prescribed binary rank -/

namespace Erdos722.FourPoint
open Finset QuadCompletion QuadSwitch Equiv
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec

abbrev markedGradient (d : ℕ) (hd : 6≤d) (c : affineBasisMarks d → Colour) :=
  weightedGradient (cubeRule d) (markedColours (cubePrivateBlocks d hd) c)

def markedDesign (d : ℕ) (hd : 6≤d) (c : affineBasisMarks d → Colour) (u : CubeOffsets d) :=
  labelledBlocks d (basisMarkedRule d hd c u)

theorem marked_design_rank (d : ℕ) (hd : 6≤d) (c : affineBasisMarks d → Colour) (u : CubeOffsets d) :
    (markedDesign d hd c u).IsBlockDesign 3 4 ∧
      (binaryIncidence (markedDesign d hd c u)).rank+(d+1)=4*2^d :=
  arbitrary_filling_rank d (rigidWord_top d (by omega)) _ (blockwise_compatible ..)

theorem marked_class_iff (d : ℕ) (hd : 6≤d) (c : affineBasisMarks d → Colour) (u v : CubeOffsets d) :
    classOf (markedDesign d hd c u)=classOf (markedDesign d hd c v) ↔
      ∃ t : Cube d → Fibre, v=u+markedGradient d hd c t := by
  rw [class_eq_iff,markedDesign,markedDesign,labelledBlocks,labelledBlocks,relabel_iso_iff]
  constructor
  · rintro ⟨e,he⟩
    obtain ⟨t,ht,_⟩ := (basis_marked_iso_iff d hd c u v e).mp he
    exact ⟨t,ht⟩
  · rintro ⟨t,ht⟩
    exact ⟨_,(basis_marked_iso_iff d hd c u v _).mpr ⟨t,ht,rfl⟩⟩

/-- This identifies the point group, including any candidate permutation of the base or fibres. -/
def markedPointGroup (d : ℕ) (hd : 6≤d) (c : affineBasisMarks d → Colour) (u : CubeOffsets d) :
    Multiplicative (markedGradient d hd c).ker ≃* automorphisms (markedDesign d hd c u) := by
  let G := markedGradient d hd c
  let f (t : Multiplicative G.ker) : automorphisms (basisMarkedRule d hd c u).blocks :=
    ⟨pointForm 1 1 t.toAdd.val,(basis_marked_iso_iff d hd c u u _).mpr
      ⟨t.toAdd.val,by rw [show G t.toAdd.val=0 from t.toAdd.prop,add_zero],rfl⟩⟩
  refine MulEquiv.trans (MulEquiv.ofBijective (f:=({toFun := f,map_one' := ?_,map_mul' := ?_} : Multiplicative G.ker →* _)) ?_)
    (automorphismRelabel (fourLabels d) _)
  · apply Subtype.ext
    apply Equiv.ext
    rintro ⟨i,x⟩
    change (i,move 1 x+0)=(i,x)
    rw [move_one,add_zero]
  · intro a b
    apply Subtype.ext
    apply Equiv.ext
    rintro ⟨i,x⟩
    change (i,move 1 x+(a.toAdd.val i+b.toAdd.val i))=(i,move 1 (move 1 x+b.toAdd.val i)+a.toAdd.val i)
    simp only [move_one]
    congr 1
    ac_rfl
  · constructor
    · intro a b eq
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      funext i
      have same := congrArg (fun e : automorphisms (basisMarkedRule d hd c u).blocks => (e.val (i,0)).2) eq
      change move 1 0+a.toAdd.val i=move 1 0+b.toAdd.val i at same
      exact add_left_cancel same
    · intro e
      obtain ⟨t,ht,form⟩ := (basis_marked_iso_iff d hd c u u e.val).mp e.prop
      have ker : G t=0 := add_left_cancel (a:=u) (ht.symm.trans (add_zero u).symm)
      exact ⟨Multiplicative.ofAdd ⟨t,ker⟩,Subtype.ext form.symm⟩

#print axioms markedGradient
#print axioms markedDesign
#print axioms marked_design_rank
#print axioms marked_class_iff
#print axioms markedPointGroup
end
end Erdos722.FourPoint
