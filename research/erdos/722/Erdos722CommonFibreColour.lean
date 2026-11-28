import Erdos722FourFibreAffineMaps
import Erdos722IntrinsicFourFibres

/-! # One linear part for all fibres of a split-system isomorphism -/

namespace Erdos722.FourPoint
open QuadCompletion Finset Equiv
variable {I J : Type*} [DecidableEq I] [DecidableEq J]

/-- The fibre component of the completion identity after the base has descended. -/
def FibreLaw (Q : Rule I) (M : Matching I) (N : Matching J) (b : I ≃ J)
    (v : I → Perm Fibre) : Prop :=
  ∀ i j k x y z, v (Q.complete i j k) (fourth M i j k x y z)=
    fourth N (b i) (b j) (b k) (v i x) (v j y) (v k z)

private theorem third [Fintype I] (size : 3≤Fintype.card I) (i j : I) (ij : i≠j) :
    ∃ k, i≠k ∧ j≠k := by
  by_contra hn
  have sub : (univ : Finset I) ⊆ {i,j} := by
    intro k _
    by_contra h
    simp only [mem_insert,mem_singleton,not_or] at h
    exact hn ⟨k,Ne.symm h.1,Ne.symm h.2⟩
  have h := card_le_card sub
  rw [card_univ,card_pair ij] at h
  omega

/-- Varying the fibre coordinate at either of two distinct base points in the
same transversal gives the same fourth point. This forces their linear parts
to agree. -/
theorem common_colour [Fintype I] (size : 3≤Fintype.card I) (o : I)
    {Q : Rule I} {M : Matching I} {N : Matching J} {b : I ≃ J} {v : I → Perm Fibre}
    (h : FibreLaw Q M N b v) :
    ∃ s : Colour, ∀ i x, v i x=move s x+v i 0 := by
  obtain ⟨s,hs⟩ := affine_fibre (v o)
  refine ⟨s,?_⟩
  intro i x
  by_cases io : i=o
  · simpa only [io] using hs x
  obtain ⟨k,ik,ok⟩ := third size i o io
  have eq₁ := h i o k x 0 0
  have eq₂ := h i o k 0 x 0
  simp only [fourth,if_neg io,if_neg ik,if_neg ok,if_neg (b.injective.ne io),
    if_neg (b.injective.ne ik),if_neg (b.injective.ne ok),add_zero,zero_add] at eq₁ eq₂
  exact add_right_cancel (calc
    v i x+v o 0 = v i 0+v o x := add_right_cancel (eq₁.symm.trans eq₂)
    _ = (move s x+v i 0)+v o 0 := by rw [hs x]; ac_rfl)

#print axioms FibreLaw
#print axioms common_colour
end Erdos722.FourPoint
