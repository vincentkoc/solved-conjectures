import Erdos722TransversalOffsets

/-! # Steiner quadruple systems from independently translated transversal sums -/

namespace Erdos722.FourPoint
open Finset QuadCompletion
open scoped Classical
noncomputable section
variable {I : Type*} [DecidableEq I] [Fintype I]

def twistedFourth (Q : Rule I) (M : Matching I) (u : BlockOffsets Q) (i j k : I) (x y z : Fibre) :=
  fourth M i j k x y z+transversalOffset Q u i j k

omit [Fintype I] in
private theorem untwist_last (M : Matching I) {i j l : I} (il : i≠l) (jl : j≠l) (x y z t : Fibre) :
    fourth M i j l x y (z+t)=fourth M i j l x y z+t := by
  by_cases eq : i=j
  · subst j; simp only [fourth,ite_true]; ac_rfl
  · simp only [fourth,if_neg eq,if_neg il,if_neg jl]; ac_rfl

private theorem twist_undo (Q : Rule I) (M : Matching I) (u : BlockOffsets Q) (i j k : I) (x y z : Fibre) :
    twistedFourth Q M u i j (Q.complete i j k) x y (twistedFourth Q M u i j k x y z)=z := by
  have cancel := congrArg Prod.snd ((fourRule Q M).cancel (i,x) (j,y) (k,z))
  change fourth M i j (Q.complete i j k) x y (fourth M i j k x y z)=z at cancel
  unfold twistedFourth
  rw [offset_cancel]
  by_cases h : transversalOffset Q u i j k=0
  · simpa only [h,add_zero] using cancel
  · have ij : i≠j := by rintro rfl; exact h (offset_repeated ..)
    have ik : i≠k := by
      rintro rfl
      exact h ((offset_swap₂ Q u i j i).trans (offset_repeated ..))
    have jk : j≠k := by
      rintro rfl
      exact h ((offset_swap₁ Q u i j j).trans ((offset_swap₂ Q u j i j).trans (offset_repeated ..)))
    have fresh := Q.fresh ij ik jk
    simp only [mem_insert,mem_singleton,not_or] at fresh
    rw [untwist_last M (Ne.symm fresh.1) (Ne.symm fresh.2.1),cancel,add_assoc,fibre_double,add_zero]

/-- Each base block has its own prescribed total in the binary plane.
Pair matchings and the base projection retain their defining equations. -/
def twistedRule (Q : Rule I) (M : Matching I) (u : BlockOffsets Q) : Rule (I × Fibre) where
  complete a b c := (Q.complete a.1 b.1 c.1,twistedFourth Q M u a.1 b.1 c.1 a.2 b.2 c.2)
  swap₁ a b c := Prod.ext (Q.swap₁ ..) (congrArg₂ (·+·)
    (congrArg Prod.snd ((fourRule Q M).swap₁ a b c)) (offset_swap₁ Q u ..))
  swap₂ a b c := Prod.ext (Q.swap₂ ..) (congrArg₂ (·+·)
    (congrArg Prod.snd ((fourRule Q M).swap₂ a b c)) (offset_swap₂ Q u ..))
  repeated a b := Prod.ext (Q.repeated ..) (by
    change fourth M a.1 a.1 b.1 a.2 a.2 b.2+transversalOffset Q u a.1 a.1 b.1=_
    rw [offset_repeated,add_zero]
    exact congrArg Prod.snd ((fourRule Q M).repeated a b))
  cancel a b c := Prod.ext (Q.cancel ..) (twist_undo Q M u ..)

theorem twisted_compatible (Q : Rule I) (M : Matching I) (u : BlockOffsets Q) :
    Compatible Q M (twistedRule Q M u) := by
  refine ⟨fun _ _ _ => rfl,fun i j x y z => ?_⟩
  change (_,fourth M i i j x y z+transversalOffset Q u i i j)=_
  rw [offset_repeated,add_zero]
  exact (fourRule_compatible Q M).pair i j x y z

theorem twisted_design (Q : Rule I) (M : Matching I) (u : BlockOffsets Q) :
    (twistedRule Q M u).blocks.IsBlockDesign 3 4 := (twistedRule Q M u).isBlockDesign

#print axioms twistedFourth
#print axioms twistedRule
#print axioms twisted_compatible
#print axioms twisted_design
end
end Erdos722.FourPoint
