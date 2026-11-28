import Erdos722TransversalIncidence

/-! # Removing the constant term from a twisted fibre isomorphism -/

namespace Erdos722.FourPoint
open QuadCompletion Equiv
noncomputable section
variable {I J : Type*} [DecidableEq I] [DecidableEq J] [Fintype I] [Fintype J]

def TwistedLaw (Q : Rule I) (R : Rule J) (M : Matching I) (N : Matching J)
    (u : BlockOffsets Q) (v : BlockOffsets R) (b : I ≃ J) (f : I → Perm Fibre) : Prop :=
  ∀ i j k x y z, f (Q.complete i j k) (twistedFourth Q M u i j k x y z)=
    twistedFourth R N v (b i) (b j) (b k) (f i x) (f j y) (f k z)

/-- The affine constant terms contain the entire effect of the block twists.
The linear parts still satisfy the homogeneous split-system law. -/
theorem twisted_frame {Q : Rule I} {R : Rule J} {M : Matching I} {N : Matching J}
    {u : BlockOffsets Q} {v : BlockOffsets R} {b : I ≃ J} {f : I → Perm Fibre}
    (size : 3≤Fintype.card I) (o : I) (h : TwistedLaw Q R M N u v b f) :
    ∃ s : Colour, Frame M N b s ∧ ∀ i x, f i x=move s x+f i 0 := by
  choose c hc using fun i => affine_fibre (f i)
  let g (i : I) : Perm Fibre := (f i).trans (Equiv.addRight (f i 0))
  have hg (i : I) (x : Fibre) : g i x=move (c i) x := by
    change f i x+f i 0=_
    rw [hc i x,add_assoc,fibre_double,add_zero]
  have eq (i j k : I) (x y z : Fibre) :
      move (c (Q.complete i j k)) (fourth M i j k x y z)+
        (move (c (Q.complete i j k)) (transversalOffset Q u i j k)+f (Q.complete i j k) 0)=
      fourth N (b i) (b j) (b k) (g i x) (g j y) (g k z)+
        (f i 0+f j 0+f k 0+transversalOffset R v (b i) (b j) (b k)) := by
    have a := h i j k x y z
    unfold twistedFourth at a
    rw [hc (Q.complete i j k) _,move_add,hc i x,hc j y,hc k z] at a
    have tr := translate_fourth N (fun l => f (b.symm l) 0) (b i) (b j) (b k)
      (move (c i) x) (move (c j) y) (move (c k) z)
    simp only [b.symm_apply_apply] at tr
    simpa only [tr,hg,add_assoc] using a
  have law : FibreLaw Q M N b g := by
    intro i j k x y z
    rw [hg]
    have const := eq i j k 0 0 0
    have zero (P : Matching I) (i j k : I) : fourth P i j k 0 0 0=0 := by simp [fourth,move_zero]
    have zero' (i j k : J) : fourth N i j k 0 0 0=0 := by simp [fourth,move_zero]
    simp only [hg,move_zero,zero,zero',zero_add] at const
    exact add_right_cancel ((eq i j k x y z).trans (by rw [const]))
  obtain ⟨s,lin⟩ := common_colour size o law
  refine ⟨s,frame_of_law law lin,fun i x => ?_⟩
  have z := lin i x
  simp only [hg,move_zero,add_zero] at z
  rw [hc i x,z]

#print axioms TwistedLaw
#print axioms twisted_frame
end
end Erdos722.FourPoint
