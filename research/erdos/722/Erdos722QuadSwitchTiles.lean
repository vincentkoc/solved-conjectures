import Erdos722QuadSwitchSheets

/-!
# Transporting the two parity classes to a labelled block

The footprint of a transversal quadruple recovers its base block. A triple
in three distinct fibres over this block has a unique completion of each parity.
-/

namespace Erdos722.QuadSwitch
open Finset
variable {V : Type*} [DecidableEq V]

def footprint (T : Finset (V × Bool)) : Finset V := T.image Prod.fst

def above (j : Fin 4 ↪ V) : Label ↪ V × Bool := j.prodMap (.refl Bool)

def tile (j : Fin 4 ↪ V) (b : Bool) : Finset (Finset (V × Bool)) :=
  (sheets b).map (mapEmbedding (above j)).toEmbedding

omit [DecidableEq V] in
theorem tile_card (j : Fin 4 ↪ V) (b : Bool) : (tile j b).card = 8 := by
  rw [tile,card_map,sheets_card]

omit [DecidableEq V] in
theorem mem_tile {j : Fin 4 ↪ V} {b : Bool} {D : Finset (V × Bool)} :
    D ∈ tile j b ↔ ∃ S ∈ sheets b, S.map (above j) = D := mem_map

omit [DecidableEq V] in
theorem tile_disjoint (j : Fin 4 ↪ V) : Disjoint (tile j false) (tile j true) := by
  apply disjoint_left.mpr
  intro D hd he
  obtain ⟨S,hs,rfl⟩ := mem_tile.mp hd
  obtain ⟨R,hr,e⟩ := mem_tile.mp he
  exact disjoint_left.mp sheets_disjoint hs ((map_injective _ e) ▸ hr)

theorem footprint_map (j : Fin 4 ↪ V) (S : Finset Label) :
    footprint (S.map (above j)) = (S.image Prod.fst).map j := by
  classical
  simp only [footprint,map_eq_image,image_image]
  rfl

theorem tile_shape {j : Fin 4 ↪ V} {b : Bool} {D : Finset (V × Bool)} (hd : D ∈ tile j b) :
    D.card = 4 ∧ footprint D = univ.map j := by
  obtain ⟨S,hs,rfl⟩ := mem_tile.mp hd
  have h := sheet_shape hs
  exact ⟨(card_map _).trans h.1,by rw [footprint_map,h.2]⟩

theorem tile_injective {j : Fin 4 ↪ V} {b : Bool} {D : Finset (V × Bool)} (hd : D ∈ tile j b) :
    Set.InjOn Prod.fst (D : Set (V × Bool)) := by
  apply injOn_of_card_image_eq
  change (footprint D).card = D.card
  rw [(tile_shape hd).2,(tile_shape hd).1,card_map]
  decide

theorem lift_subset (j : Fin 4 ↪ V) {T : Finset (V × Bool)} (hs : footprint T ⊆ univ.map j) :
    ∃ S : Finset Label, S.map (above j) = T := by
  classical
  let S := univ.filter fun x : Label => above j x ∈ T
  refine ⟨S,?_⟩
  ext ⟨x,y⟩
  constructor
  · rintro h
    obtain ⟨u,hu,e⟩ := mem_map.mp h
    exact e ▸ (mem_filter.mp hu).2
  · intro h
    obtain ⟨i,_,hi⟩ := mem_map.mp (hs (mem_image.mpr ⟨(x,y),h,rfl⟩))
    exact mem_map.mpr ⟨(i,y),mem_filter.mpr ⟨mem_univ _,by simpa [above,hi] using h⟩,Prod.ext hi rfl⟩

theorem tile_completion (j : Fin 4 ↪ V) (b : Bool) {T : Finset (V × Bool)}
    (ht : T.card = 3) (hp : (footprint T).card = 3) (hs : footprint T ⊆ univ.map j) :
    ∃! D, D ∈ tile j b ∧ T ⊆ D := by
  obtain ⟨S,hS⟩ := lift_subset j hs
  have h3 : S.card = 3 := by simpa only [← hS,card_map] using ht
  have hp3 : (S.image Prod.fst).card = 3 := by
    simpa only [← hS,footprint_map,card_map] using hp
  obtain ⟨A,ha,unique⟩ := card_eq_one_iff_existsUnique.mp (sheet_triple b S h3 hp3)
  obtain ⟨ha₁,ha₂⟩ := mem_filter.mp ha
  refine ⟨A.map (above j),⟨mem_tile.mpr ⟨A,ha₁,rfl⟩,hS ▸ map_subset_map.mpr ha₂⟩,?_⟩
  rintro D ⟨hd,hsub⟩
  obtain ⟨R,hr,rfl⟩ := mem_tile.mp hd
  rw [← hS] at hsub
  rw [unique R (mem_filter.mpr ⟨hr,map_subset_map.mp hsub⟩)]

noncomputable def chart (B : Finset V) (h : B.card = 4) : Fin 4 ↪ V :=
  (B.equivFinOfCardEq h).symm.toEmbedding.trans (Function.Embedding.subtype _)

omit [DecidableEq V] in
theorem chart_range (B : Finset V) (h : B.card = 4) : univ.map (chart B h) = B := by
  ext x
  constructor
  · intro hx
    obtain ⟨i,_,rfl⟩ := mem_map.mp hx
    exact ((B.equivFinOfCardEq h).symm i).property
  · intro hx
    let i := B.equivFinOfCardEq h ⟨x,hx⟩
    exact mem_map.mpr ⟨i,mem_univ _,congrArg Subtype.val ((B.equivFinOfCardEq h).symm_apply_apply ⟨x,hx⟩)⟩

#print axioms tile_shape
#print axioms tile_completion
#print axioms chart_range

end Erdos722.QuadSwitch
