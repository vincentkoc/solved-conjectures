import Erdos722TwistedFourFibreRule
import Erdos722FourFibreGroups

/-! # Fibre translations and the incidence map on transversal offsets -/

namespace Erdos722.FourPoint
open Finset QuadCompletion
open scoped Classical
noncomputable section
variable {I : Type*} [DecidableEq I] [Fintype I]

/-- Translating each fibre changes the prescribed sum on a block by its incidence sum. -/
def blockGradient (Q : Rule I) : (I → Fibre) →+ BlockOffsets Q where
  toFun t B := ∑ i ∈ B.val, t i
  map_zero' := by ext B <;> simp
  map_add' t v := by funext B; exact Finset.sum_add_distrib

theorem offset_add (Q : Rule I) (u v : BlockOffsets Q) (i j k : I) :
    transversalOffset Q (u+v) i j k=transversalOffset Q u i j k+transversalOffset Q v i j k := by
  unfold transversalOffset offsetAt
  split <;> simp

theorem offset_gradient (Q : Rule I) (t : I → Fibre) (i j k : I) :
    transversalOffset Q (blockGradient Q t) i j k=t i+t j+t k+t (Q.complete i j k) := by
  by_cases ij : i=j
  · subst j; rw [offset_repeated,Q.repeated,fibre_double,zero_add,fibre_double]
  by_cases ik : i=k
  · subst k; rw [offset_swap₂,offset_repeated,Q.swap₂,Q.repeated]
    rw [add_assoc (t i) (t j),add_comm (t j) (t i),← add_assoc,fibre_double,zero_add,fibre_double]
  by_cases jk : j=k
  · subst k; rw [offset_swap₁,offset_swap₂,offset_repeated,Q.swap₁,Q.swap₂,Q.repeated]
    rw [add_assoc (t i),fibre_double,add_zero,fibre_double]
  have fresh := Q.fresh ij ik jk
  rw [offset_on_block Q _ ij ik jk]
  change ∑ a ∈ insert (Q.complete i j k) {i,j,k}, t a=_
  rw [sum_insert fresh,sum_insert (by simp [ij,ik]),sum_insert (by simpa using jk),sum_singleton]
  ac_rfl

theorem gradient_kernel (Q : Rule I) : (blockGradient Q).ker=shifts Q := by
  ext t
  change blockGradient Q t=0 ↔ Offset Q t
  have z (i j k : I) : transversalOffset Q 0 i j k=0 := by
    unfold transversalOffset offsetAt
    split <;> rfl
  constructor
  · intro h i j k
    have eq := offset_gradient Q t i j k
    rw [h,z] at eq
    exact (show ∀ a b : Fibre, 0=a+b → b=a by decide +kernel) _ _ eq
  · intro h
    apply offset_injective Q
    funext i j k
    rw [offset_gradient,z,h i j k,fibre_double]

#print axioms blockGradient
#print axioms offset_add
#print axioms offset_gradient
#print axioms gradient_kernel
end
end Erdos722.FourPoint
