import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-! # Counting matching words determined on a set of edges -/

namespace Erdos722.FourPoint
open Finset
open scoped Classical
noncomputable section
variable {E A : Type*} [Fintype E] [Fintype A]

/-- Restrict to the free edges. If the remaining coordinates are individually
prescribed by this restriction, each free word has exactly one extension. -/
theorem determined_edges (S : Finset E) (fill : ((i : E) → i∉S → A) → (i : E) → i∈S → A) :
    ((univ : Finset (E → A)).filter fun w => ∀ i (h : i∈S), w i=fill (fun j _ => w j) i h).card =
      (Fintype.card A)^(Fintype.card E-S.card) := by
  classical
  let T := (univ : Finset (E → A)).filter fun w => ∀ i (h : i∈S), w i=fill (fun j _ => w j) i h
  let F := {i : E // i∉S}
  let extend (u : F → A) (i : E) : A :=
    if h : i∈S then fill (fun j hj => u ⟨j,hj⟩) i h else u ⟨i,h⟩
  have outside (u : F → A) (j : E) (h : j∉S) : extend u j=u ⟨j,h⟩ := by simp [extend,h]
  let e : T ≃ (F → A) :=
    { toFun := fun w i => w.val i.val
      invFun := fun u => ⟨extend u,mem_filter.mpr ⟨mem_univ _,by
        intro i hi
        have rest : (fun j (_ : j∉S) => extend u j)=(fun j hj => u ⟨j,hj⟩) := by
          funext j hj
          exact outside u j hj
        rw [rest]
        simp [extend,hi]⟩⟩
      left_inv := fun w => by
        apply Subtype.ext
        funext i
        by_cases h : i∈S
        · exact (dif_pos h).trans (((mem_filter.mp w.prop).2 i h).symm)
        · exact dif_neg h
      right_inv := fun u => funext fun i => outside u i.val i.prop }
  have size : Fintype.card F=Fintype.card E-S.card := by
    let ec : F ≃ ↥((univ : Finset E)\S) := Equiv.subtypeEquivRight (by simp)
    rw [Fintype.card_congr ec,Fintype.card_coe,card_sdiff,inter_univ,card_univ]
  exact (Nat.card_eq_finsetCard T).symm.trans ((Nat.card_congr e).trans (by
    rw [Nat.card_eq_fintype_card,Fintype.card_fun,size]))

/-- A matching comparison with another row fixes the entries on the first
row when all its comparison edges lie outside the selected row. -/
theorem linked_edges (S : Finset E) (dst : E → E) (away : ∀ i∈S, dst i∉S) (colour : E → A → A) :
    ((univ : Finset (E → A)).filter fun w => ∀ i∈S,w i=colour i (w (dst i))).card =
      (Fintype.card A)^(Fintype.card E-S.card) :=
  determined_edges S (fun rest i hi => colour i (rest (dst i) (away i hi)))

#print axioms determined_edges
#print axioms linked_edges
end
end Erdos722.FourPoint
