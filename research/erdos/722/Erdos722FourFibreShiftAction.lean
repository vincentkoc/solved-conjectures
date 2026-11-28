import Erdos722FourFibreGroups

/-! # The natural action of the matching stabilizer on binary translations -/

namespace Erdos722.FourPoint
open QuadCompletion Equiv
variable {I : Type*} {Q : Rule I} {M : Matching I}

/-- Conjugation changes a shift by moving its base argument and applying
the common permutation of the three nonzero fibre vectors. -/
def moveShift (g : baseFrames Q M) (t : shifts Q) : shifts Q :=
  ⟨fun i => move g.val.2 (t.val (g.val.1.symm i)),by
    intro i j k
    have h := (g⁻¹).prop.1 i j k
    change g.val.1.symm (Q.complete i j k)=Q.complete (g.val.1.symm i) (g.val.1.symm j) (g.val.1.symm k) at h
    change move g.val.2 (t.val (g.val.1.symm (Q.complete i j k)))=_
    rw [h,t.prop,move_add,move_add]⟩

private theorem moveShift_one (t : shifts Q) : moveShift (1 : baseFrames Q M) t=t :=
  Subtype.ext (funext fun i => move_one (t.val i))

private theorem moveShift_mul (g h : baseFrames Q M) (t : shifts Q) :
    moveShift (g*h) t=moveShift g (moveShift h t) :=
  Subtype.ext (funext fun _ => move_product ..)

private theorem moveShift_add (g : baseFrames Q M) (u t : shifts Q) :
    moveShift g (u+t)=moveShift g u+moveShift g t :=
  Subtype.ext (funext fun _ => move_add ..)

def shiftAction : baseFrames Q M →* MulAut (Multiplicative (shifts Q)) where
  toFun g := {
    toFun := fun t => Multiplicative.ofAdd (moveShift g t.toAdd)
    invFun := fun t => Multiplicative.ofAdd (moveShift g⁻¹ t.toAdd)
    left_inv := fun t => by
      apply Multiplicative.toAdd.injective
      change moveShift g⁻¹ (moveShift g t.toAdd)=t.toAdd
      rw [← moveShift_mul,inv_mul_cancel,moveShift_one]
    right_inv := fun t => by
      apply Multiplicative.toAdd.injective
      change moveShift g (moveShift g⁻¹ t.toAdd)=t.toAdd
      rw [← moveShift_mul,mul_inv_cancel,moveShift_one]
    map_mul' := fun u t => congrArg Multiplicative.ofAdd (moveShift_add g u.toAdd t.toAdd) }
  map_one' := by
    apply MulEquiv.ext
    exact fun t => congrArg Multiplicative.ofAdd (moveShift_one t.toAdd)
  map_mul' := by
    intro g h
    apply MulEquiv.ext
    exact fun t => congrArg Multiplicative.ofAdd (moveShift_mul g h t.toAdd)

#print axioms moveShift
#print axioms shiftAction
end Erdos722.FourPoint
