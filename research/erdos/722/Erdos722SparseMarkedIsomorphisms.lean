import Erdos722CubeMarkedCoefficients
import Erdos722WeightedBlockTranslations

/-! # Unrestricted point isomorphisms of sparsely marked four-fibre fillings -/

namespace Erdos722.FourPoint
open Finset QuadCompletion QuadSwitch Equiv
noncomputable section
variable {I : Type*} [DecidableEq I] [Fintype I]

/-- Binary checks recover the fibres. Ordinary transversals at one common
unmarked point then recover the global colour and the base matching. -/
theorem rigid_marked_iso {Q : Rule I} {M : Matching I} (hyp : FibreHypotheses Q M)
    (size : 3≤Fintype.card I) (rigid : Subsingleton (baseFrames Q M))
    (C : IncidenceColours Q) (u v : BlockOffsets Q)
    (plain : ∀ b : Perm I, ∃ o, PlainThrough (colouredRule Q M C u) o ∧
      PlainThrough (colouredRule Q M C v) (b o)) (e : Perm (I × Fibre)) :
    e.finsetCongr.finsetCongr (colouredRule Q M C u).blocks=(colouredRule Q M C v).blocks ↔
      ∃ t : I → Fibre, v=u+weightedGradient Q C t ∧ e=pointForm 1 1 t := by
  constructor
  · intro h
    let P := colouredRule Q M C u
    let T := colouredRule Q M C v
    have src : Compatible Q M P := blockwise_compatible ..
    have dst : Compatible Q M T := blockwise_compatible ..
    obtain ⟨root,star⟩ := hyp.star
    have same (i j : I) (x y : Fibre) : i=j ↔ (e (i,x)).1=(e (j,y)).1 := by
      have eq := sameChecks_relabel e P.blocks (i,x) (j,y)
      rw [show e.finsetCongr.finsetCongr P.blocks=T.blocks from h] at eq
      exact (sameChecks_four hyp.separates src star hyp.noFix _ _).symm.trans
        (eq.trans (sameChecks_four hyp.separates dst star hyp.noFix _ _))
    obtain ⟨b,f,coord⟩ := fibre_coordinates 0 e same
    have ec (p : I × Fibre) : e p=(b p.1,f p.1 p.2) := coord p.1 p.2
    have comp (i j k : I) (x y z : Fibre) :
        (b (Q.complete i j k),f (Q.complete i j k) (P.complete (i,x) (j,y) (k,z)).2)=
        T.complete (b i,f i x) (b j,f j y) (b k,f k z) := by
      have eq := completion_of_blocks P T e h (i,x) (j,y) (k,z)
      rwa [ec (P.complete ..),src.project,coord,coord,coord] at eq
    obtain ⟨o,hp,ht⟩ := plain b
    obtain ⟨s,frame,lin⟩ := frame_at_plain_point src dst o size hp ht
      (fun i j k x y z => congrArg Prod.snd (comp i j k x y z))
    have base (i j k : I) : b (Q.complete i j k)=Q.complete (b i) (b j) (b k) :=
      (congrArg Prod.fst (comp i j k 0 0 0)).trans (dst.project ..)
    have one : (⟨(b,s),base,frame⟩ : baseFrames Q M)=1 := rigid.elim _ _
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (show (b,s)=(1,1) from congrArg Subtype.val one)
    have form : e=pointForm 1 1 (fun i => f i 0) := by
      apply Equiv.ext
      rintro ⟨i,x⟩
      rw [coord,lin]
      rfl
    rw [form] at h
    exact ⟨_,(translation_coloured_iff M C u v _).mp h,form⟩
  · rintro ⟨t,eq,rfl⟩
    exact (translation_coloured_iff M C u v t).mpr eq

attribute [local instance] cubeOrder cubeDec

abbrev markedMatching (d : ℕ) (hd : 6≤d) := edgeMatching 0 (rigidWord d (by omega : 2≤d))

abbrev basisMarkedRule (d : ℕ) (hd : 6≤d) (c : affineBasisMarks d → Colour) (u : CubeOffsets d) :=
  colouredRule (cubeRule d) (markedMatching d hd) (markedColours (cubePrivateBlocks d hd) c) u

abbrev markedRule (d : ℕ) (hd : 6≤d) := basisMarkedRule d hd (fun _ => threeCycle)

theorem basis_marked_iso_iff (d : ℕ) (hd : 6≤d) (c : affineBasisMarks d → Colour)
    (u v : CubeOffsets d) (e : Perm (Cube d × Fibre)) :
    e.finsetCongr.finsetCongr (basisMarkedRule d hd c u).blocks=(basisMarkedRule d hd c v).blocks ↔
      ∃ t : Cube d → Fibre, v=u+weightedGradient (cubeRule d) (markedColours (cubePrivateBlocks d hd) c) t ∧
        e=pointForm 1 1 t := by
  have two : 2≤d := by omega
  have hw := rigidWord_top d two
  have hyp : FibreHypotheses (cubeRule d) (markedMatching d hd) :=
    ⟨cube_separates d,⟨0,edge_normalized 0 _⟩,(noFix_edge_iff ..).mpr hw⟩
  have size : 3≤Fintype.card (Cube d) := by
    simpa [Cube] using (show 3≤2^d by have := sparse_basis_size hd; omega)
  apply rigid_marked_iso hyp size (path_word_frames d two)
  intro b
  obtain ⟨o,src,dst⟩ := common_unmarked_point d hd b
  exact ⟨o,marked_plain _ u _ _ src,marked_plain _ v _ _ dst⟩

theorem cycle_iso_iff (d : ℕ) (hd : 6≤d) (u v : CubeOffsets d) (e : Perm (Cube d × Fibre)) :
    e.finsetCongr.finsetCongr (markedRule d hd u).blocks=(markedRule d hd v).blocks ↔
      ∃ t : Cube d → Fibre, v=u+weightedGradient (cubeRule d) (cycleCoefficients d hd) t ∧ e=pointForm 1 1 t :=
  basis_marked_iso_iff d hd _ u v e

#print axioms rigid_marked_iso
#print axioms markedMatching
#print axioms basisMarkedRule
#print axioms basis_marked_iso_iff
#print axioms markedRule
#print axioms cycle_iso_iff
end
end Erdos722.FourPoint
