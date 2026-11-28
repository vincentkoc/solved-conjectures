import Erdos478ConsecutiveReturnPairs

/-! # The number and total length of returns in a collection of fibres -/

namespace Erdos478.ReturnConcentration
open Finset
open scoped Classical
noncomputable section

variable {α : Type*} [DecidableEq α]

def fibre (v : ℕ → α) (A : Finset ℕ) (y : α) := A.filter (fun i => v i = y)

def returns (v : ℕ → α) (A : Finset ℕ) :=
  (A.image v).biUnion fun y => links (fibre v A y)

def totalWidth (v : ℕ → α) (A : Finset ℕ) :=
  ∑ y ∈ A.image v,width (fibre v A y)

private theorem separate (v : ℕ → α) (A : Finset ℕ) :
    (↑(A.image v) : Set α).PairwiseDisjoint (fun y => links (fibre v A y)) := by
  intro x _ y _ ne
  apply Finset.disjoint_left.mpr
  intro e ex ey
  exact ne ((mem_filter.mp (links_mem ex).1).2.symm.trans (mem_filter.mp (links_mem ey).1).2)

/-- Exactly one selected index, the first occurrence, is omitted per represented value. -/
theorem returns_card (v : ℕ → α) (A : Finset ℕ) :
    (returns v A).card + (A.image v).card = A.card := by
  rw [returns,card_biUnion (separate v A),card_eq_sum_ones (A.image v),← sum_add_distrib]
  rw [card_eq_sum_card_image v A]
  apply sum_congr rfl
  intro y hy
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
  have h := card_pos.mpr (show (fibre v A (v i)).Nonempty from ⟨i,mem_filter.mpr ⟨hi,rfl⟩⟩)
  change (links (fibre v A (v i))).card + 1 = (fibre v A (v i)).card
  rw [links_card]
  omega

theorem returns_sum (v : ℕ → α) (A : Finset ℕ) :
    ∑ e ∈ returns v A,(e.2-e.1) = totalWidth v A := by
  rw [returns,sum_biUnion (separate v A)]
  exact sum_congr rfl fun _ _ => links_sum _

theorem returns_mem {v : ℕ → α} {A : Finset ℕ} {e : ℕ × ℕ} (he : e ∈ returns v A) :
    e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 < e.2 ∧ v e.1 = v e.2 := by
  obtain ⟨_,_,h⟩ := mem_biUnion.mp he
  obtain ⟨ha,hb,hlt⟩ := links_mem h
  obtain ⟨ha,va⟩ := mem_filter.mp ha
  obtain ⟨hb,vb⟩ := mem_filter.mp hb
  exact ⟨ha,hb,hlt,va.trans vb.symm⟩

theorem totalWidth_le {a b : ℕ} {A : Finset ℕ} (v : ℕ → α) (hA : A ⊆ Icc a b) :
    totalWidth v A ≤ (A.image v).card*(b-a) := by
  calc
    _ ≤ ∑ _ ∈ A.image v, (b-a) := sum_le_sum fun _ _ => width_le ((filter_subset ..).trans hA)
    _ = _ := by simp

#print axioms fibre
#print axioms returns
#print axioms totalWidth
#print axioms returns_card
#print axioms returns_sum
#print axioms returns_mem
#print axioms totalWidth_le

end
end Erdos478.ReturnConcentration
