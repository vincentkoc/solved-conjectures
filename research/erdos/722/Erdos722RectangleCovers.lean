import Erdos722PointedTiles

/-!
# Relabelling local triple covers

A cover can be built on field coordinates and transported to the two
canonical finite ordinals. Transposition exchanges the two trace conditions.
-/

namespace Erdos722.PointedProduct
open Finset Function
noncomputable section

structure TripleCover {X : Type*} (k : ℕ) (accept : Finset X → Prop) where
  blocks : Finset (Finset X)
  size : ∀ B∈blocks, B.card=k
  inside : ∀ B∈blocks, ∀ T⊆B, T.card=3 → accept T
  cover : ∀ T, T.card=3 → accept T → ∃! B, B∈blocks ∧ T⊆B

def TripleCover.relabel {X Y : Type*} {k : ℕ} {P : Finset X → Prop} {Q : Finset Y → Prop}
    (C : TripleCover k P) (e : X ≃ Y) (h : ∀ T, Q (T.map e.toEmbedding) ↔ P T) :
    TripleCover k Q := by
  classical
  refine ⟨C.blocks.image (Finset.map e.toEmbedding),?_,?_,?_⟩
  · intro B hB
    obtain ⟨B,hmem,rfl⟩ := mem_image.mp hB
    simpa using C.size B hmem
  · intro B hB T hT hc
    obtain ⟨B,hmem,rfl⟩ := mem_image.mp hB
    obtain ⟨T,rfl⟩ := e.finsetCongr.surjective T
    exact (h T).mpr (C.inside B hmem T (map_subset_map.mp hT) (by simpa using hc))
  · intro T hT ha
    obtain ⟨T,rfl⟩ := e.finsetCongr.surjective T
    obtain ⟨B,⟨hB,hTB⟩,hu⟩ := C.cover T (by simpa using hT) ((h T).mp ha)
    refine ⟨B.map e.toEmbedding,⟨mem_image_of_mem _ hB,map_subset_map.mpr hTB⟩,?_⟩
    rintro D ⟨hD,hTD⟩
    obtain ⟨D,hm,rfl⟩ := mem_image.mp hD
    exact congrArg (Finset.map _) (hu D ⟨hm,map_subset_map.mp hTD⟩)

variable {U V : Type*} [DecidableEq U] [DecidableEq V]

omit [DecidableEq V] in
theorem mem_leftTrace {T : Finset (Grid U V)} {x : U} :
    x∈leftTrace T ↔ ∃ y, some (x,y)∈T := by
  constructor
  · intro h
    obtain ⟨⟨a,b⟩,hm,rfl⟩ := mem_image.mp h
    exact ⟨b,mem_eraseNone.mp hm⟩
  · rintro ⟨y,hy⟩
    exact mem_image.mpr ⟨(x,y),mem_eraseNone.mpr hy,rfl⟩

omit [DecidableEq U] in
theorem mem_rightTrace {T : Finset (Grid U V)} {y : V} :
    y∈rightTrace T ↔ ∃ x, some (x,y)∈T := by
  constructor
  · intro h
    obtain ⟨⟨a,b⟩,hm,rfl⟩ := mem_image.mp h
    exact ⟨a,mem_eraseNone.mp hm⟩
  · rintro ⟨x,hx⟩
    exact mem_image.mpr ⟨(x,y),mem_eraseNone.mpr hx,rfl⟩

abbrev RectangleCover (q : ℕ) (s t : Shape) (U V : Type*) [DecidableEq U] [DecidableEq V] :=
  TripleCover (q+1) (localEvent (U:=U) (V:=V) s t)

def RectangleCover.transpose {q s t} (C : RectangleCover q s t U V) : RectangleCover q t s V U := by
  let e : Grid U V ≃ Grid V U := (Equiv.prodComm U V).optionCongr
  apply C.relabel e
  intro T
  have hl : leftTrace (T.map e.toEmbedding)=rightTrace T := by
    ext y
    simp only [mem_leftTrace,mem_rightTrace,mem_map_equiv]
    rfl
  have hr : rightTrace (T.map e.toEmbedding)=leftTrace T := by
    ext x
    simp only [mem_leftTrace,mem_rightTrace,mem_map_equiv]
    rfl
  simp only [localEvent,hl,hr,and_comm]

def RectangleCover.tile {q s t} [Fintype U] [Fintype V] (C : RectangleCover q s t U V)
    (hu : Fintype.card U=s.width q) (hv : Fintype.card V=t.width q) : Tile q s t := by
  let e := Fintype.equivFinOfCardEq hu
  let f := Fintype.equivFinOfCardEq hv
  let g := (e.prodCongr f).optionCongr
  have h (T : Finset (Grid U V)) : localEvent s t (T.map g.toEmbedding) ↔ localEvent s t T := by
    change localEvent s t (T.map (gridMap e.toEmbedding f.toEmbedding)) ↔ _
    obtain ⟨hl,hr⟩ := traces_map e.toEmbedding f.toEmbedding T
    simp [localEvent,hl,hr]
  let D := C.relabel g h
  exact ⟨D.blocks,D.size,D.inside,D.cover⟩

#print axioms TripleCover.relabel
#print axioms RectangleCover.transpose
#print axioms RectangleCover.tile
end
end Erdos722.PointedProduct
