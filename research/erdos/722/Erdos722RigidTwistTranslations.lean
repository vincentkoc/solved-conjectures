import Erdos722TwistedPointIsomorphisms
import Erdos722SplitFourAutomorphismGroup

/-! # Classification by the incidence range for a rigid matching -/

namespace Erdos722.FourPoint
open QuadCompletion QuadSwitch Equiv
noncomputable section
variable {I : Type*} [DecidableEq I] [Fintype I] {Q : Rule I} {M : Matching I}

theorem translation_offset_iff (u v : BlockOffsets Q) (t : I → Fibre) :
    OffsetLaw Q Q u v (1 : Perm I) 1 t ↔ v=u+blockGradient Q t := by
  have eq (i j k : I) :
      (transversalOffset Q u i j k+t (Q.complete i j k)=t i+t j+t k+transversalOffset Q v i j k) ↔
      transversalOffset Q v i j k=transversalOffset Q (u+blockGradient Q t) i j k := by
    rw [offset_add,offset_gradient]
    exact (show ∀ a b c z : Fibre, (a+b=c+z) ↔ z=a+(c+b) by decide +kernel) _ _ _ _
  constructor
  · intro h
    apply offset_injective Q
    funext i j k
    exact (eq i j k).mp (by simpa only [move_one,Perm.one_apply] using h i j k)
  · intro h i j k
    simp only [move_one,Perm.one_apply]
    exact (eq i j k).mpr (congrArg (fun w => transversalOffset Q w i j k) h)

theorem rigid_twist_iso (hyp : FibreHypotheses Q M) (size : 3≤Fintype.card I)
    (rigid : Subsingleton (baseFrames Q M)) (u v : BlockOffsets Q) (e : Perm (I × Fibre)) :
    e.finsetCongr.finsetCongr (twistedRule Q M u).blocks=(twistedRule Q M v).blocks ↔
      ∃ t : I → Fibre, v=u+blockGradient Q t ∧ e=pointForm 1 1 t := by
  rw [twisted_iso_iff hyp hyp size]
  constructor
  · rintro ⟨b,s,t,base,frame,law,rfl⟩
    have f : (⟨(b,s),base,frame⟩ : baseFrames Q M)=1 := rigid.elim _ _
    have eq : (b,s)=(1,1) := congrArg Subtype.val f
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    exact ⟨t,(translation_offset_iff ..).mp law,rfl⟩
  · rintro ⟨t,h,rfl⟩
    exact ⟨1,1,t,fun _ _ _ => rfl,(1 : baseFrames Q M).prop.2,(translation_offset_iff ..).mpr h,rfl⟩

/-- The full point group is the same subgroup for every offset on a rigid frame. -/
theorem twisted_aut_eq (hyp : FibreHypotheses Q M) (size : 3≤Fintype.card I)
    (rigid : Subsingleton (baseFrames Q M)) (u : BlockOffsets Q) :
    automorphisms (twistedRule Q M u).blocks=automorphisms (fourRule Q M).blocks := by
  ext e
  change (e.finsetCongr.finsetCongr _=_) ↔ e.finsetCongr.finsetCongr _=_
  rw [rigid_twist_iso hyp size rigid,four_fibre_iso_iff hyp hyp size]
  constructor
  · rintro ⟨t,h,rfl⟩
    have ker : blockGradient Q t=0 := add_left_cancel (a:=u) (h.symm.trans (add_zero u).symm)
    have shift : t∈shifts Q := gradient_kernel Q ▸ (show t∈(blockGradient Q).ker from ker)
    exact ⟨1,1,t,fun _ _ _ => rfl,(1 : baseFrames Q M).prop.2,shift,rfl⟩
  · rintro ⟨b,s,t,base,frame,shift,rfl⟩
    have f : (⟨(b,s),base,frame⟩ : baseFrames Q M)=1 := rigid.elim _ _
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (show (b,s)=(1,1) from congrArg Subtype.val f)
    have ker : t∈(blockGradient Q).ker := (gradient_kernel Q).symm ▸ (show t∈shifts Q from shift)
    exact ⟨t,by rw [show blockGradient Q t=0 from ker,add_zero],rfl⟩

#print axioms translation_offset_iff
#print axioms rigid_twist_iso
#print axioms twisted_aut_eq
end
end Erdos722.FourPoint
