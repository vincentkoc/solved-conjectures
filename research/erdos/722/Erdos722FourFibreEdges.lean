import Erdos722FourFibreChecks
import Mathlib.Data.Finset.Prod

/-! # Independent direction matchings away from a normalized star -/

namespace Erdos722.FourPoint
open Finset QuadCompletion
variable {I : Type*} [LinearOrder I] [Fintype I]

/-- One oriented copy of each unordered nonstar edge. -/
def edges (o : I) : Finset (I × I) :=
  let S := (univ : Finset I).erase o
  (S ×ˢ S).filter fun p => p.1<p.2

theorem mem_edges (o i j : I) : (i,j)∈edges o ↔ (i≠o ∧ j≠o) ∧ i<j := by simp [edges]

theorem edges_card (o : I) : (edges o).card=(Fintype.card I-1).choose 2 := by
  rw [edges,card_product_filter_lt,card_erase_of_mem (mem_univ o),card_univ]

def edgeMove (o : I) (w : edges o → Colour) (i j : I) : Colour :=
  if h : (i,j)∈edges o then w ⟨(i,j),h⟩
  else if h : (j,i)∈edges o then (w ⟨(j,i),h⟩)⁻¹ else 1

def edgeMatching (o : I) (w : edges o → Colour) : Matching I where
  transport := edgeMove o w
  diagonal i := by simp [edgeMove,mem_edges]
  reverse i j := by
    have excl (a : (i,j)∈edges o) (b : (j,i)∈edges o) : False :=
      lt_asymm ((mem_edges ..).mp a).2 ((mem_edges ..).mp b).2
    by_cases a : (i,j)∈edges o <;> by_cases b : (j,i)∈edges o <;> simp_all [edgeMove]

theorem edge_normalized (o : I) (w : edges o → Colour) : Normalized (edgeMatching o w) o := by
  intro i
  simp [edgeMatching,edgeMove,mem_edges]

theorem edge_forward (o : I) (w : edges o → Colour) (e : edges o) :
    (edgeMatching o w).transport e.val.1 e.val.2=w e := by
  simp [edgeMatching,edgeMove,e.prop]

theorem invariant_iff_edges (o : I) (w : edges o → Colour) (c : Option Direction) :
    (∀ i j, c.map ((edgeMatching o w).transport i j)=c) ↔ ∀ e, c.map (w e)=c := by
  constructor
  · intro h e
    simpa only [edge_forward] using h e.val.1 e.val.2
  · intro h i j
    change c.map (edgeMove o w i j)=c
    unfold edgeMove
    split
    · apply h
    · split
      · exact (show ∀ s : Colour, ∀ a : Option Direction, a.map s=a → a.map (s⁻¹ : Colour)=a
          by intro s a ha; cases a with
             | none => rfl
             | some a => exact congrArg some (s.symm_apply_eq.mpr (Option.some.inj ha).symm)) _ _ (h _)
      · cases c <;> rfl

#print axioms edges
#print axioms mem_edges
#print axioms edges_card
#print axioms edgeMove
#print axioms edgeMatching
#print axioms edge_normalized
#print axioms edge_forward
#print axioms invariant_iff_edges
end Erdos722.FourPoint
