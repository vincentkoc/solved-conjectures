import Erdos722SmallIncidenceCertificates
import Mathlib.Data.List.Sublists

/-! # Checking finite design certificates at arbitrary strength

Enumerate only the r-subsets of the point list. For each one count the
incident columns directly, using the integer row masks.
-/

namespace Erdos722.SmallOrders
open Finset

def testedRows (ps : List ℕ) (r b : ℕ) : Bool :=
  ((List.finRange ps.length).sublistsLen r).all fun xs =>
    ((List.range b).countP fun j => xs.all fun x => (ps.get x).testBit j)==1

theorem design_of_tested_rows {ps : List ℕ} {r k b : ℕ}
    (sizes : ∀ j<b, (column ps j).card=k) (checked : testedRows ps r b=true) :
    (blocks ps b).IsBlockDesign r k := by
  constructor
  · intro B h
    obtain ⟨j,hj,rfl⟩ := mem_image.mp h
    exact sizes j (mem_range.mp hj)
  · intro A hA
    let xs := (List.finRange ps.length).filter fun x => decide (x∈A)
    have mem (x : Fin ps.length) : x∈xs ↔ x∈A := by simp [xs]
    have eq : xs.toFinset=A := Finset.ext fun x => List.mem_toFinset.trans (mem x)
    have len : xs.length=r := by
      rw [← List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _),eq,hA]
    have hxs : xs∈(List.finRange ps.length).sublistsLen r :=
      List.mem_sublistsLen.mpr ⟨List.filter_sublist,len⟩
    let P (j : ℕ) := xs.all fun x => (ps.get x).testBit j
    have cnt : (List.range b).countP P=1 := of_decide_eq_true (by
      simpa only [beq_iff_eq,decide_eq_true_eq] using List.all_eq_true.mp checked xs hxs)
    have hit (j : ℕ) : P j=true ↔ A⊆column ps j := by
      change xs.all _=true ↔ _
      rw [List.all_eq_true]
      simp only [mem]
      exact forall₂_congr fun x _ => by simp [column]
    let cols := (List.range b).toFinset.filter (fun j => P j=true)
    have num : cols.card=1 := by
      rw [show cols=(List.range b).toFinset.filter (fun j => P j=true) from rfl,
        (List.nodup_range).card_eq_countP]
      simpa using cnt
    obtain ⟨j,e⟩ := card_eq_one.mp num
    have one (i : ℕ) : i<b ∧ A⊆column ps i ↔ i=j := by
      rw [← mem_singleton,← e]
      simp [cols,hit]
    obtain ⟨lt,sub⟩ := (one j).mpr rfl
    refine ⟨column ps j,⟨mem_image_of_mem _ (mem_range.mpr lt),sub⟩,?_⟩
    rintro B ⟨hB,hsub⟩
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hB
    rw [(one i).mp ⟨mem_range.mp hi,hsub⟩]

#print axioms testedRows
#print axioms design_of_tested_rows
end Erdos722.SmallOrders
