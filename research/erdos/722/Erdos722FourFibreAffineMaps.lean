import Erdos722FourFibreRule

/-! # The affine permutations of the four-point fibre -/

namespace Erdos722.FourPoint
open Equiv
local instance : Fintype (Perm Fibre) := fintypePerm
local instance : Fintype Colour := fintypePerm

theorem affine_fibre : ∀ v : Perm Fibre, ∃ s : Colour, ∀ x, v x=move s x+v 0 := by
  decide +kernel

theorem move_faithful {s r : Colour} (h : ∀ x, move s x=move r x) : s=r := by
  apply Equiv.ext
  intro d
  simpa only [move_vector,direction_vector] using congrArg direction (h (vector d))

theorem move_product : ∀ s r x, move (s*r) x=move s (move r x) := by decide +kernel

private theorem twice_shift : ∀ x y a : Fibre, (x+a)+(y+a)=x+y := by decide +kernel

/-- The offsets in a repeated-fibre pair cancel before its matching is applied. -/
theorem translate_fourth {I : Type*} [DecidableEq I] (M : Matching I) (t : I → Fibre)
    (i j k : I) (x y z : Fibre) :
    fourth M i j k (x+t i) (y+t j) (z+t k)=fourth M i j k x y z+(t i+t j+t k) := by
  by_cases ij : i=j
  · subst j
    simp only [fourth,ite_true,twice_shift,fibre_double,zero_add]
    ac_rfl
  by_cases ik : i=k
  · subst k
    simp only [fourth,if_neg ij,ite_true,twice_shift]
    rw [show t i+t j+t i=t j by rw [add_comm (t i) (t j),add_assoc,fibre_double,add_zero]]
    ac_rfl
  by_cases jk : j=k
  · subst k
    simp only [fourth,if_neg ij,ite_true,twice_shift]
    rw [add_assoc (t i) (t j),fibre_double,add_zero]
    ac_rfl
  simp only [fourth,if_neg ij,if_neg ik,if_neg jk]
  ac_rfl

#print axioms affine_fibre
#print axioms move_faithful
#print axioms move_product
#print axioms translate_fourth
end Erdos722.FourPoint
