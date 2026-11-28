import Erdos722QuadSwitchTiles

/-!
# Independent doubling of the blocks of a Steiner quadruple system

Over each original block choose one of the two transversal parity classes.
Every pair of complete point fibres also supplies a block.
-/

namespace Erdos722.QuadSwitch
open Finset
variable {V : Type*} [DecidableEq V] {H : Finset (Finset V)}

def twins (P : Finset V) : Finset (V × Bool) := P ×ˢ univ

theorem footprint_twins (P : Finset V) : footprint (twins P) = P := by
  ext x
  constructor
  · intro h
    obtain ⟨y,hy,rfl⟩ := mem_image.mp h
    exact (mem_product.mp hy).1
  · intro h
    exact mem_image.mpr ⟨(x,false),mem_product.mpr ⟨h,mem_univ _⟩,rfl⟩

theorem subset_twins (T : Finset (V × Bool)) (P : Finset V) :
    T ⊆ twins P ↔ footprint T ⊆ P := by
  constructor
  · intro h
    rw [← footprint_twins P]
    exact image_mono Prod.fst h
  · intro h x hx
    exact mem_product.mpr ⟨h (mem_image.mpr ⟨x,hx,rfl⟩),mem_univ _⟩

omit [DecidableEq V] in
theorem twins_card (P : Finset V) : (twins P).card = P.card * 2 := by
  simp [twins]

noncomputable def component (hH : H.IsBlockDesign 3 4) (i : H) (b : Bool) :=
  tile (chart i.val (hH.1 _ i.property)) b

theorem component_shape (hH : H.IsBlockDesign 3 4) (i : H) {b : Bool} {D : Finset (V × Bool)}
    (h : D ∈ component hH i b) : D.card = 4 ∧ footprint D = i.val :=
  ⟨(tile_shape h).1,(tile_shape h).2.trans (chart_range _ _)⟩

variable [Fintype V]

/-- The labelled doubling for the chosen parity on every original block. -/
noncomputable def doubling (hH : H.IsBlockDesign 3 4) (bits : H → Bool) :
    Finset (Finset (V × Bool)) :=
  ((univ.powersetCard 2).image twins) ∪ univ.biUnion (fun i => component hH i (bits i))

theorem mem_doubling (hH : H.IsBlockDesign 3 4) (bits : H → Bool) (D : Finset (V × Bool)) :
    D ∈ doubling hH bits ↔ (∃ P : Finset V, P.card = 2 ∧ twins P = D) ∨
      ∃ i : H, D ∈ component hH i (bits i) := by
  simp [doubling]

theorem doubling_design (hH : H.IsBlockDesign 3 4) (bits : H → Bool) :
    (doubling hH bits).IsBlockDesign 3 4 := by
  classical
  constructor
  · intro D h
    rcases (mem_doubling hH bits D).mp h with ⟨P,hp,rfl⟩ | ⟨i,hi⟩
    · rw [twins_card,hp]
    · exact (component_shape hH i hi).1
  intro T ht
  let P := footprint T
  have pt : T ⊆ twins P := (subset_twins T P).mpr Subset.rfl
  have small : P.card ≤ 3 := ht ▸ card_image_le
  by_cases hp : P.card = 3
  · obtain ⟨B,⟨hb,hpB⟩,uniqueB⟩ := hH.2 P hp
    let i : H := ⟨B,hb⟩
    let j := chart B (hH.1 _ hb)
    have hj : univ.map j = B := chart_range _ _
    obtain ⟨D,⟨hd,htD⟩,uniqueD⟩ := tile_completion j (bits i) ht hp (hj.symm ▸ hpB)
    refine ⟨D,⟨(mem_doubling hH bits D).mpr (Or.inr ⟨i,hd⟩),htD⟩,?_⟩
    rintro D' ⟨hd',hT'⟩
    rcases (mem_doubling hH bits D').mp hd' with ⟨Q,hq,rfl⟩ | ⟨i',hi'⟩
    · have hle := card_le_card ((subset_twins T Q).mp hT')
      change P.card ≤ Q.card at hle
      omega
    · have hsub : P ⊆ i'.val := (component_shape hH i' hi').2 ▸ image_mono Prod.fst hT'
      have e : i' = i := Subtype.ext (uniqueB i'.val ⟨i'.property,hsub⟩)
      subst i'
      exact uniqueD D' ⟨hi',hT'⟩
  · have bound := card_le_card pt
    rw [twins_card,ht] at bound
    have p2 : P.card = 2 := by omega
    refine ⟨twins P,⟨(mem_doubling hH bits _).mpr (Or.inl ⟨P,p2,rfl⟩),pt⟩,?_⟩
    rintro D ⟨hd,htD⟩
    rcases (mem_doubling hH bits D).mp hd with ⟨Q,hq,rfl⟩ | ⟨i,hi⟩
    · have eq : P = Q := eq_of_subset_of_card_le ((subset_twins T Q).mp htD) (by omega)
      rw [eq]
    · have inj := (tile_injective hi).mono (show (T : Set (V × Bool)) ⊆ D from htD)
      exact False.elim (hp ((card_image_of_injOn inj).trans ht))

#print axioms mem_doubling
#print axioms doubling_design

end Erdos722.QuadSwitch
