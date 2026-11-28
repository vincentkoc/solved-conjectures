import Erdos722PointedTiles

/-!
# Gluing two pointed triple designs

A local design for each pair of face shapes suffices for a design on the
product of the punctured point sets with one common point at infinity.
-/

namespace Erdos722.PointedProduct
open Finset Function

private theorem pull_subset {A X : Type*} [DecidableEq X] (e : A ↪ X)
    {T : Finset X} {B : Finset A} (h : T⊆B.map e) :
    ∃ S⊆B, Finset.map e S=T := by
  rw [map_eq_image] at h
  obtain ⟨S,hS,he⟩ := subset_image_iff.mp h
  exact ⟨S,hS,(map_eq_image _ _).trans he⟩

variable {q : ℕ} {U V : Type*} [DecidableEq U] [DecidableEq V]
variable {H : Finset (Finset (Option U))} {J : Finset (Finset (Option V))}

/-- Every triple in a transported block belongs to the faces which supplied it. -/
private theorem faces_of_block (hH : H.IsBlockDesign 3 (q+1)) (hJ : J.IsBlockDesign 3 (q+1))
    (tile : ∀ s t, Tile q s t) {a : Face H} {b : Face J} {B} (hB : B∈(tile (kind a) (kind b)).blocks)
    {T : Finset (Grid U V)} (ht : T.card=3) (hs : T⊆B.map (place hH hJ a b)) :
    belongs a b T := by
  obtain ⟨S,hS,rfl⟩ := pull_subset _ hs
  exact (belongs_place hH hJ a b S).mpr ((tile _ _).inside B hB S hS (by simpa using ht))

/-- The relative product theorem for a supplied family of local templates. -/
theorem pointed_product [Fintype U] [Fintype V] (tile : ∀ s t, Tile q s t)
    (hH : H.IsBlockDesign 3 (q+1)) (hJ : J.IsBlockDesign 3 (q+1)) :
    ∃ G : Finset (Finset (Grid U V)), G.IsBlockDesign 3 (q+1) := by
  classical
  let G : Finset (Finset (Grid U V)) := univ.filter fun C => ∃ a b B,
    B∈(tile (kind a) (kind b)).blocks ∧ B.map (place hH hJ a b)=C
  have memG (C) : C∈G ↔ ∃ a b B,
      B∈(tile (kind a) (kind b)).blocks ∧ B.map (place hH hJ a b)=C := by simp [G]
  refine ⟨G,?_,?_⟩
  · intro C hc
    obtain ⟨a,b,B,hB,rfl⟩ := (memG _).mp hc
    simpa using (tile (kind a) (kind b)).size B hB
  · intro T ht
    obtain ⟨⟨a,b⟩,hab,uf⟩ := unique_pair hH hJ ht
    obtain ⟨S,hST⟩ := in_place hH hJ hab
    have hc : S.card=3 := by rw [← hST,card_map] at ht; exact ht
    have hl := (belongs_place hH hJ a b S).mp (hST.symm ▸ hab)
    obtain ⟨B,⟨hB,hSB⟩,ub⟩ := (tile (kind a) (kind b)).cover S hc hl
    refine ⟨B.map (place hH hJ a b),⟨(memG _).mpr ⟨a,b,B,hB,rfl⟩,hST ▸ map_subset_map.mpr hSB⟩,?_⟩
    rintro C ⟨hC,hTC⟩
    obtain ⟨a',b',D,hD,rfl⟩ := (memG _).mp hC
    have hp := uf (a',b') (faces_of_block hH hJ tile hD ht hTC)
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hp
    have hSD : S⊆D := map_subset_map.mp (hST.symm ▸ hTC)
    exact congrArg (Finset.map _) (ub D ⟨hD,hSD⟩)

/-- Transport a canonical block design along a bijection of point sets. -/
theorem relabel_design {A X : Type*} [DecidableEq X] {r k : ℕ} (e : A ≃ X)
    {G : Finset (Finset A)} (hG : G.IsBlockDesign r k) :
    (G.image (Finset.map e.toEmbedding)).IsBlockDesign r k := by
  classical
  constructor
  · rintro _ hc
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hc
    simpa using hG.1 B hB
  · intro T ht
    obtain ⟨B,⟨hB,hTB⟩,uniq⟩ := hG.2 (T.map e.symm.toEmbedding) (by simpa using ht)
    refine ⟨B.map e.toEmbedding,⟨mem_image_of_mem _ hB,map_symm_subset.mp hTB⟩,?_⟩
    rintro _ ⟨hC,hTC⟩
    obtain ⟨C,hmem,rfl⟩ := mem_image.mp hC
    exact congrArg (Finset.map _) (uniq C ⟨hmem,map_symm_subset.mpr hTC⟩)

def ExistsDesign (q n : ℕ) := ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 3 (q+1)

/-- The order of the pointed product is ab+1, including the vacuous orders. -/
theorem order_product (tile : ∀ s t, Tile q s t) {a b : ℕ}
    (ha : ExistsDesign q (a+1)) (hb : ExistsDesign q (b+1)) : ExistsDesign q (a*b+1) := by
  classical
  obtain ⟨H,hH⟩ := ha
  obtain ⟨J,hJ⟩ := hb
  let e (n : ℕ) := (Fintype.equivFinOfCardEq (by simp : Fintype.card (Option (Fin n))=n+1)).symm
  obtain ⟨G,hG⟩ := pointed_product tile (relabel_design (e a) hH) (relabel_design (e b) hJ)
  let g := Fintype.equivFinOfCardEq (by simp [Grid] : Fintype.card (Grid (Fin a) (Fin b))=a*b+1)
  exact ⟨_,relabel_design g hG⟩

#print axioms pointed_product
#print axioms relabel_design
#print axioms order_product
end Erdos722.PointedProduct
