import Erdos722QuadSwitchCube
import Erdos722MinimumDesignDistance

/-!
# Rigidity of the transversal replacement

Any family of transversals with the same triple counts as one parity class
must be one of the two parity classes. The minimum trade distance forces
a nontrivial exchange to use all eight blocks on each side.
-/

namespace Erdos722.QuadSwitch
open Finset Trade
variable {V : Type*} [DecidableEq V]

theorem tile_exhaust (j : Fin 4 ↪ V) {D : Finset (V × Bool)} (hc : D.card = 4)
    (hp : footprint D = univ.map j) : D ∈ tile j false ∪ tile j true := by
  obtain ⟨S,rfl⟩ := lift_subset j hp.subset
  rw [footprint_map] at hp
  have h := section_exhaust S (by simpa using hc) (map_injective j hp)
  rcases mem_union.mp h with h | h
  · exact mem_union_left _ (mem_tile.mpr ⟨S,h,rfl⟩)
  · exact mem_union_right _ (mem_tile.mpr ⟨S,h,rfl⟩)

variable [Fintype V]

theorem rigid_tile (j : Fin 4 ↪ V) (C : Finset (Finset (V × Bool)))
    (allowed : C ⊆ tile j false ∪ tile j true)
    (rows : ∀ I : Finset (V × Bool), I.card = 3 → countThrough C I = countThrough (tile j false) I) :
    C = tile j false ∨ C = tile j true := by
  classical
  by_cases e : C = tile j false
  · exact Or.inl e
  right
  have hc (D : Finset (V × Bool)) (hD : D ∈ C) : D.card = 4 := by
    rcases mem_union.mp (allowed hD) with h | h <;> exact (tile_shape h).1
  obtain ⟨h₁,h₂⟩ := packing_distance (by decide : 3 ≤ 4) hc (fun _ h => (tile_shape h).1) rows e
  have full : tile j false \ C = tile j false := eq_of_subset_of_card_le sdiff_subset
    (by simpa only [tile_card] using (show 8 ≤ (tile j false \ C).card from h₂))
  have csub : C ⊆ tile j true := by
    intro D hD
    apply (mem_union.mp (allowed hD)).resolve_left
    intro h
    exact (mem_sdiff.mp (full.symm ▸ h)).2 hD
  apply eq_of_subset_of_card_le csub
  rw [tile_card]
  exact h₁.trans (card_le_card sdiff_subset)

variable {H : Finset (Finset V)}

/-- The projection of every block is an original block or the block is two entire point fibres. -/
def Compatible (H : Finset (Finset V)) (D : Finset (Finset (V × Bool))) : Prop :=
  ∀ B ∈ D, (∃ P : Finset V, P.card = 2 ∧ twins P = B) ∨ footprint B ∈ H

def overBlock (D : Finset (Finset (V × Bool))) (B : Finset V) := D.filter (fun T => footprint T = B)

omit [Fintype V] in
theorem local_rows (hH : H.IsBlockDesign 3 4) (i : H) {D : Finset (Finset (V × Bool))}
    (hD : D.IsBlockDesign 3 4) (compat : Compatible H D) (T : Finset (V × Bool)) (ht : T.card = 3) :
    countThrough (overBlock D i.val) T = countThrough (component hH i false) T := by
  let j := chart i.val (hH.1 _ i.property)
  have hj : univ.map j = i.val := chart_range _ _
  have admiss {B : Finset (V × Bool)} (hc : B.card = 4) (hb : footprint B = i.val) (hs : T ⊆ B) :
      (footprint T).card = 3 ∧ footprint T ⊆ i.val := by
    have inj : Set.InjOn Prod.fst (B : Set (V × Bool)) := injOn_of_card_image_eq
      (by change (footprint B).card = B.card; rw [hb,hc,hH.1 i.val i.property])
    exact ⟨(card_image_of_injOn (inj.mono hs)).trans ht,hb ▸ image_mono Prod.fst hs⟩
  by_cases h : (footprint T).card = 3 ∧ footprint T ⊆ i.val
  · obtain ⟨B,⟨hb,hs⟩,ub⟩ := hD.2 T ht
    have base_eq : footprint B = i.val := by
      rcases compat B hb with ⟨P,hp,rfl⟩ | hbase
      · have le := card_le_card ((subset_twins T P).mp hs)
        omega
      · have uq := hH.2 (footprint T) h.1
        exact uq.unique ⟨hbase,image_mono Prod.fst hs⟩ ⟨i.property,h.2⟩
    have a : countThrough (overBlock D i.val) T = 1 := by
      apply card_eq_one_iff_existsUnique.mpr
      refine ⟨B,mem_filter.mpr ⟨mem_filter.mpr ⟨hb,base_eq⟩,hs⟩,?_⟩
      intro B' hB'
      exact ub B' ⟨(mem_filter.mp (mem_filter.mp hB').1).1,(mem_filter.mp hB').2⟩
    have b := tile_completion j false ht h.1 (hj.symm ▸ h.2)
    rw [a]
    symm
    apply card_eq_one_iff_existsUnique.mpr
    simpa only [mem_filter,component,j] using b
  · have a : countThrough (overBlock D i.val) T = 0 := by
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro B hB
      obtain ⟨hb,hs⟩ := mem_filter.mp hB
      obtain ⟨hBD,he⟩ := mem_filter.mp hb
      exact h (admiss (hD.1 _ hBD) he hs)
    have b : countThrough (component hH i false) T = 0 := by
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro B hB
      obtain ⟨hb,hs⟩ := mem_filter.mp hB
      have shape := component_shape hH i hb
      exact h (admiss shape.1 shape.2 hs)
    exact a.trans b.symm

theorem component_rigidity (hH : H.IsBlockDesign 3 4) (i : H) {D : Finset (Finset (V × Bool))}
    (hD : D.IsBlockDesign 3 4) (compat : Compatible H D) :
    ∃ b : Bool, overBlock D i.val = component hH i b := by
  let j := chart i.val (hH.1 _ i.property)
  have allowed : overBlock D i.val ⊆ tile j false ∪ tile j true := by
    intro B hB
    obtain ⟨hb,eq⟩ := mem_filter.mp hB
    exact tile_exhaust j (hD.1 B hb) (eq.trans (chart_range _ _).symm)
  rcases rigid_tile j _ allowed (local_rows hH i hD compat) with h | h
  · exact ⟨false,h⟩
  · exact ⟨true,h⟩

#print axioms rigid_tile
#print axioms local_rows
#print axioms component_rigidity
end Erdos722.QuadSwitch
