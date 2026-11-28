import Erdos722CommonFibreColour
import Erdos722CompletionIsomorphisms

/-! # The exact equations on the colour, the base map and the translation -/

namespace Erdos722.FourPoint
open QuadCompletion QuadSwitch Equiv
variable {I J : Type*} [DecidableEq I] [DecidableEq J]

def Frame (M : Matching I) (N : Matching J) (b : I ≃ J) (s : Colour) : Prop :=
  ∀ i j, s*M.transport i j=N.transport (b i) (b j)*s

def Offset (Q : Rule I) (t : I → Fibre) : Prop :=
  ∀ i j k, t (Q.complete i j k)=t i+t j+t k

private theorem fourth_zero (M : Matching I) (i j k : I) : fourth M i j k 0 0 0=0 := by
  simp [fourth,move_zero]

theorem offset_of_law {Q : Rule I} {M : Matching I} {N : Matching J} {b : I ≃ J}
    {v : I → Perm Fibre} (h : FibreLaw Q M N b v) : Offset Q (fun i => v i 0) := by
  intro i j k
  have a := h i j k 0 0 0
  rw [fourth_zero] at a
  have c := translate_fourth N (fun j => v (b.symm j) 0) (b i) (b j) (b k) 0 0 0
  simp only [Equiv.symm_apply_apply,zero_add,fourth_zero] at c
  exact a.trans c

theorem frame_of_law {Q : Rule I} {M : Matching I} {N : Matching J} {b : I ≃ J}
    {v : I → Perm Fibre} (h : FibreLaw Q M N b v) {s : Colour}
    (lin : ∀ i x, v i x=move s x+v i 0) : Frame M N b s := by
  intro i j
  apply move_faithful
  intro x
  have a := h i i j 0 x 0
  simp only [Q.repeated,fourth,ite_true,zero_add] at a
  rw [lin j (move (M.transport i j) x),lin i x] at a
  rw [(show ∀ u z : Fibre, u+(z+u)=z by decide +kernel) (v i 0) (move s x),add_comm (v j 0)] at a
  simpa only [move_product] using add_right_cancel a

theorem map_fourth {M : Matching I} {N : Matching J} {b : I ≃ J} {s : Colour}
    (h : Frame M N b s) (i j k : I) (x y z : Fibre) :
    move s (fourth M i j k x y z)=fourth N (b i) (b j) (b k) (move s x) (move s y) (move s z) := by
  have step (u v : I) (a : Fibre) : move s (move (M.transport u v) a)=
      move (N.transport (b u) (b v)) (move s a) := by
    rw [← move_product,← move_product,h u v]
  simp only [fourth,EmbeddingLike.apply_eq_iff_eq]
  split_ifs <;> simp only [move_add,step]

private theorem shift_twice : ∀ x t : Fibre, x+t+t=x := by decide +kernel

/-- The affine permutation in each fibre, with its base map. -/
def pointForm (b : I ≃ J) (s : Colour) (t : I → Fibre) : I × Fibre ≃ J × Fibre where
  toFun p := (b p.1,move s p.2+t p.1)
  invFun p := (b.symm p.1,move s⁻¹ (p.2+t (b.symm p.1)))
  left_inv p := by simp only [Equiv.symm_apply_apply,shift_twice,move_inv]
  right_inv p := by
    simp only [Equiv.apply_symm_apply,← move_product,mul_inv_cancel,move_one,shift_twice]

theorem form_preserves [Fintype I] [Fintype J] {Q : Rule I} {R : Rule J} {M : Matching I} {N : Matching J}
    {b : I ≃ J} (base : ∀ i j k, b (Q.complete i j k)=R.complete (b i) (b j) (b k))
    {s : Colour} (frame : Frame M N b s) {t : I → Fibre} (shift : Offset Q t) :
    (pointForm b s t).finsetCongr.finsetCongr (fourRule Q M).blocks=(fourRule R N).blocks := by
  apply blocks_of_completion
  rintro ⟨i,x⟩ ⟨j,y⟩ ⟨k,z⟩
  refine Prod.ext (base i j k) ?_
  change move s (fourth M i j k x y z)+t (Q.complete i j k)=
    fourth N (b i) (b j) (b k) (move s x+t i) (move s y+t j) (move s z+t k)
  have ht := translate_fourth N (fun j => t (b.symm j)) (b i) (b j) (b k) (move s x) (move s y) (move s z)
  simpa only [Equiv.symm_apply_apply,shift i j k,map_fourth frame] using ht.symm

#print axioms Frame
#print axioms Offset
#print axioms offset_of_law
#print axioms frame_of_law
#print axioms map_fourth
#print axioms pointForm
#print axioms form_preserves
end Erdos722.FourPoint
