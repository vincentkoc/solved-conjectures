import Erdos722FourFibreDirections
import Erdos722QuadCompletion

/-! # Quadruple systems with three independently matched directions between fibres -/

namespace Erdos722.FourPoint
open QuadCompletion Finset
variable {I : Type*} [DecidableEq I]

/-- A perfect-matching bijection for each ordered pair of distinct four-point fibres. -/
structure Matching (I : Type*) where
  transport : I → I → Colour
  diagonal (i) : transport i i=1
  reverse (i j) : transport j i=(transport i j)⁻¹

def fourth (M : Matching I) (i j k : I) (x y z : Fibre) : Fibre :=
  if i=j then z+move (M.transport i k) (x+y)
  else if i=k then y+move (M.transport i j) (x+z)
  else if j=k then x+move (M.transport j i) (y+z)
  else x+y+z

private theorem twice (x y : Fibre) : x+(x+y)=y := by rw [← add_assoc,fibre_double,zero_add]

private theorem middle {A} (Q : Rule A) (a b : A) : Q.complete a b a=b := by
  rw [Q.swap₂,Q.repeated]

private theorem last {A} (Q : Rule A) (a b : A) : Q.complete a b b=a := by
  rw [Q.swap₁,middle]

private theorem exchange₁ (M : Matching I) (i j k : I) (x y z : Fibre) :
    fourth M i j k x y z=fourth M j i k y x z := by
  by_cases hij : i=j
  · subst j; simp [fourth,add_comm x y]
  · simp only [fourth,if_neg hij,if_neg (Ne.symm hij)]
    by_cases hik : i=k <;> by_cases hjk : j=k <;> simp_all [add_comm x y]

private theorem exchange₂ (M : Matching I) (i j k : I) (x y z : Fibre) :
    fourth M i j k x y z=fourth M i k j x z y := by
  by_cases hij : i=j <;> by_cases hik : i=k <;> by_cases hjk : j=k <;>
    simp_all [fourth,M.diagonal,move_one,add_comm,add_left_comm,eq_comm]

private theorem undo (Q : Rule I) (M : Matching I) (i j k : I) (x y z : Fibre) :
    fourth M i j (Q.complete i j k) x y (fourth M i j k x y z)=z := by
  by_cases hij : i=j
  · subst j
    simp [fourth,Q.repeated,add_assoc,fibre_double]
  by_cases hik : i=k
  · subst k
    simp [fourth,hij,middle,twice,M.reverse i j,move_inv]
  by_cases hjk : j=k
  · subst k
    simp [fourth,hij,last,twice,M.reverse j i,move_inv]
  have fresh := Q.fresh hij hik hjk
  simp only [mem_insert,mem_singleton,not_or] at fresh
  simp [fourth,hij,hik,hjk,Ne.symm fresh.1,Ne.symm fresh.2.1,twice]

/-- Transversal blocks have zero total fibre sum. The pair matchings are arbitrary. -/
def fourRule (Q : Rule I) (M : Matching I) : Rule (I × Fibre) where
  complete a b c := (Q.complete a.1 b.1 c.1,fourth M a.1 b.1 c.1 a.2 b.2 c.2)
  swap₁ _ _ _ := Prod.ext (Q.swap₁ ..) (exchange₁ ..)
  swap₂ _ _ _ := Prod.ext (Q.swap₂ ..) (exchange₂ ..)
  repeated a b := Prod.ext (Q.repeated ..) (by simp [fourth,fibre_double,move_zero])
  cancel a b c := Prod.ext (Q.cancel ..) (undo ..)

theorem fourRule_design [Fintype I] (Q : Rule I) (M : Matching I) :
    (fourRule Q M).blocks.IsBlockDesign 3 4 := Rule.isBlockDesign _

#print axioms Matching
#print axioms fourth
#print axioms fourRule
#print axioms fourRule_design
end Erdos722.FourPoint
