import Erdos722UnitExcessArithmetic
import Mathlib.NumberTheory.Bertrand

/-! # Tits's bound and a first possible order at each rank

Around an uncovered (r+1)-set the r-faces determine blocks with disjoint
exterior parts. Together with the unit-excess arithmetic this bounds the
minimum over all nontrivial block sizes.
-/

namespace Erdos722.UnitExcess
open Finset IntegralDesign

private theorem uncovered {r k n : ℕ} (hrk : r≤k) (hkn : k<n)
    {H : Finset (Finset (Fin n))} (hH : H.IsBlockDesign r k) :
    ∃ T : Finset (Fin n), T.card=r+1 ∧ ∀ B∈H, ¬T⊆B := by
  obtain ⟨A,_,hA⟩ := exists_subset_card_eq (s:=(univ : Finset (Fin n))) (n:=r) (by simp; omega)
  obtain ⟨B,⟨hB,sub⟩,unique⟩ := hH.2 A hA
  have pos : 0<((univ : Finset (Fin n))\B).card := by
    rw [card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin,hH.1 B hB]; omega
  obtain ⟨x,hx⟩ := card_pos.mp pos
  have no := (mem_sdiff.mp hx).2
  refine ⟨insert x A,by rw [card_insert_of_notMem (fun h => no (sub h)),hA],?_⟩
  intro C hC hTC
  obtain rfl := unique C ⟨hC,(subset_insert _ _).trans hTC⟩
  exact no (hTC (mem_insert_self ..))

theorem tits_bound {r k n : ℕ} (hr : 0<r) (hrk : r≤k) (hkn : k<n)
    {H : Finset (Finset (Fin n))} (hH : H.IsBlockDesign r k) : (r+1)*(k-r+1)≤n := by
  classical
  obtain ⟨T,hT,none⟩ := uncovered hrk hkn hH
  have face (i : T) : (T.erase i.val).card=r := by rw [card_erase_of_mem i.prop,hT]; omega
  choose B hh using fun i : T => (hH.2 _ (face i)).exists
  have miss (i : T) : i.val∉B i := fun hi => none _ (hh i).1 (by
    simpa only [insert_erase i.prop] using insert_subset hi (hh i).2)
  let E (i : T) := B i\(T.erase i.val)
  have outside (i : T) {x : Fin n} (hx : x∈E i) : x∉T := by
    intro ht
    obtain ⟨hb,hn⟩ := mem_sdiff.mp hx
    have ne : x≠i.val := fun e => miss i (e ▸ hb)
    exact hn (mem_erase.mpr ⟨ne,ht⟩)
  have dis {i j : T} (ne : i≠j) : Disjoint (E i) (E j) := by
    apply disjoint_left.mpr
    intro x hxi hxj
    have neq : i.val≠j.val := Subtype.coe_injective.ne ne
    have hj : j.val∈T.erase i.val := mem_erase.mpr ⟨neq.symm,j.prop⟩
    let Z := (T.erase i.val).erase j.val
    have zcard : Z.card=r-1 := by rw [show Z=(T.erase i.val).erase j.val from rfl,card_erase_of_mem hj,face]
    have xi : x∉Z := fun h => outside i hxi (mem_erase.mp (mem_erase.mp h).2).2
    have sz : (insert x Z).card=r := by rw [card_insert_of_notMem xi,zcard]; omega
    have left : insert x Z⊆B i := insert_subset (mem_sdiff.mp hxi).1 ((erase_subset _ _).trans (hh i).2)
    have right : insert x Z⊆B j := insert_subset (mem_sdiff.mp hxj).1 (by
      intro y hy
      exact (hh j).2 (mem_erase.mpr ⟨(mem_erase.mp hy).1,(mem_erase.mp (mem_erase.mp hy).2).2⟩))
    have eq := (hH.2 _ sz).unique ⟨(hh i).1,left⟩ ⟨(hh j).1,right⟩
    exact miss i (eq ▸ (hh j).2 (mem_erase.mpr ⟨neq,i.prop⟩))
  let P (i : T) := insert i.val (E i)
  have pd : (Set.univ : Set T).PairwiseDisjoint P := by
    intro i _ j _ ne
    apply disjoint_left.mpr
    intro x hi hj
    rcases mem_insert.mp hi with rfl|hi
    · rcases mem_insert.mp hj with eq|hj
      · exact ne (Subtype.ext eq)
      · exact outside j hj i.prop
    · rcases mem_insert.mp hj with rfl|hj
      · exact outside i hi j.prop
      · exact disjoint_left.mp (dis ne) hi hj
  have size (i : T) : (P i).card=k-r+1 := by
    rw [show P i=insert i.val (E i) from rfl,card_insert_of_notMem (fun h => outside i h i.prop)]
    rw [show E i=B i\(T.erase i.val) from rfl,card_sdiff_of_subset (hh i).2,hH.1 _ (hh i).1,face]
  have cnt := card_le_univ ((univ : Finset T).biUnion P)
  rw [card_biUnion (by simpa only [coe_univ] using pd)] at cnt
  simpa only [size,sum_const,card_univ,Fintype.card_coe,hT,nsmul_eq_mul,Nat.cast_id,Fintype.card_fin] using cnt

#print axioms tits_bound
end Erdos722.UnitExcess
