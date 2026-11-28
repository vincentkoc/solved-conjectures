import Erdos722FourFibreShiftAction
import Erdos722VerticalAutomorphismGroup

/-! # The full automorphism group of a split four-fibre quadruple system -/

namespace Erdos722.FourPoint
open QuadCompletion QuadSwitch Equiv
variable {I : Type*} [DecidableEq I] [Fintype I] (Q : Rule I) (M : Matching I)

abbrev FrameProduct := (Multiplicative (shifts Q)) ⋊[shiftAction] (baseFrames Q M)

private def inputShift (g : baseFrames Q M) (v : shifts Q) : shifts Q :=
  ⟨fun i => v.val (g.val.1 i),fun i j k => by dsimp only; rw [g.prop.1,v.prop]⟩

private def outputShift (g : baseFrames Q M) (v : shifts Q) : shifts Q :=
  inputShift Q M g⁻¹ v

def evaluateFrame : FrameProduct Q M →* automorphisms (fourRule Q M).blocks where
  toFun z := ⟨pointForm z.right.val.1 z.right.val.2 (inputShift Q M z.right z.left.toAdd).val,
    form_preserves z.right.prop.1 z.right.prop.2 (inputShift Q M z.right z.left.toAdd).prop⟩
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    rintro ⟨i,x⟩
    exact Prod.ext rfl (show move 1 x+0=x by rw [move_one,add_zero])
  map_mul' := by
    intro a b
    apply Subtype.ext
    apply Equiv.ext
    rintro ⟨i,x⟩
    refine Prod.ext ?_ ?_
    · rfl
    let A := a.right.val.1
    let B := b.right.val.1
    let U := a.left.toAdd.val
    let V := b.left.toAdd.val
    let s := a.right.val.2
    let r := b.right.val.2
    change move (s*r) x+(U (A (B i))+move s (V (A.symm (A (B i)))))=
      move s (move r x+V (B i))+U (A (B i))
    rw [Equiv.symm_apply_apply,move_product,move_add]
    ac_rfl

theorem evaluateFrame_injective (o : I) : Function.Injective (evaluateFrame Q M) := by
  intro a b eq
  have e := congrArg (fun z : automorphisms (fourRule Q M).blocks => z.val) eq
  obtain ⟨base,col,sh⟩ := pointForm_unique o e
  have g : a.right=b.right := Subtype.ext (Prod.ext base col)
  have v : a.left=b.left := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext j
    have h := congrFun sh (a.right.val.1.symm j)
    change a.left.toAdd.val (a.right.val.1 (a.right.val.1.symm j))=
      b.left.toAdd.val (b.right.val.1 (a.right.val.1.symm j)) at h
    simpa only [base,Equiv.apply_symm_apply] using h
  exact SemidirectProduct.ext v g

/-- A group isomorphism to the stabilizer of the actual block family, including
all automorphisms that move the normalized star. -/
noncomputable def fullFourAut (hyp : FibreHypotheses Q M) (size : 3≤Fintype.card I) :
    FrameProduct Q M ≃* automorphisms (fourRule Q M).blocks := by
  apply MulEquiv.ofBijective (evaluateFrame Q M)
  obtain ⟨o,_⟩ := hyp.star
  refine ⟨evaluateFrame_injective Q M o,?_⟩
  intro e
  obtain ⟨b,s,t,base,frame,shift,he⟩ := (four_fibre_iso_iff hyp hyp size e.val).mp e.prop
  let g : baseFrames Q M := ⟨(b,s),base,frame⟩
  let u : shifts Q := ⟨t,shift⟩
  refine ⟨⟨Multiplicative.ofAdd (outputShift Q M g u),g⟩,Subtype.ext ?_⟩
  rw [he]
  apply Equiv.ext
  rintro ⟨i,x⟩
  change (b i,move s x+t (b.symm (b i)))=(b i,move s x+t i)
  rw [Equiv.symm_apply_apply]

theorem fullFourAut_card (hyp : FibreHypotheses Q M) (size : 3≤Fintype.card I) :
    Nat.card (automorphisms (fourRule Q M).blocks)=Nat.card (Checks Q.blocks)^2*Nat.card (baseFrames Q M) := by
  rw [← Nat.card_congr (fullFourAut Q M hyp size).toEquiv,
    Nat.card_congr (SemidirectProduct.equivProd : FrameProduct Q M ≃ _),Nat.card_prod]
  exact congrArg (·*Nat.card (baseFrames Q M)) (shifts_card Q)

#print axioms FrameProduct
#print axioms evaluateFrame
#print axioms evaluateFrame_injective
#print axioms fullFourAut
#print axioms fullFourAut_card
end Erdos722.FourPoint
