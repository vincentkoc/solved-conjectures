import Erdos722AffineStarBlockLayout

/-! # A small protected pencil and nonlinear markers covering its complement -/

namespace Erdos722.AffineStar
open Finset QuadCompletion FourPoint QuadSwitch LatinFillings
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec

/-- The exterior supports fixed linear equations. Every nonroot point meets a marked interior block. -/
structure Layout (d : ℕ) (hd : 6≤d) where
  exterior : Finset (Finset (Base d))
  markers : Finset (Finset (Base d))
  sub : exterior ⊆ (cubeRule (d+2)).blocks
  pencil_sub : pencil (cubeRule (d+2)) 0 ⊆ exterior
  marked : markers ⊆ (cubeRule (d+2)).blocks \ exterior
  cover (i : Base d) : i≠0 → ∃ B∈markers, i∈B
  exterior_bound : exterior.card ≤ (pencil (cubeRule (d+2)) 0).card+2*2^(d+2)
  marker_bound : markers.card ≤ 2^(d+2)-1
  detects (t : Base d → Fibre) : (∀ B : (cubeRule (d+2)).blocks, B.val∈exterior →
    weightedGradient (cubeRule (d+2)) (colours d hd) t B=0) → t=0

theorem layout_exists (d : ℕ) (hd : 6≤d) : Nonempty (Layout d hd) := by
  let Q := cubeRule (d+2)
  obtain ⟨K,hK,small,det⟩ := sparse_gradient d hd
  let E := pencil Q 0 ∪ K
  have count : Fintype.card (Base d)=2^(d+2) := by simp [Base,Cube]
  have large : 64≤Fintype.card (Base d) := by
    rw [count]
    exact Nat.pow_le_pow_right (by decide : 0<2) (show 6≤d+2 by omega)
  let U := (univ : Finset (Base d)).erase 0
  have hit (x : U) : ∃ B∈Q.blocks, x.val∈B ∧ (0:Base d)∉B ∧ B∉K :=
    marker_exists Q (ne_of_mem_erase x.prop) large K (count ▸ small)
  choose mark spec using hit
  let F := univ.image mark
  refine ⟨⟨E,F,union_subset (filter_subset ..) hK,subset_union_left,?_,?_,
    (card_union_le ..).trans (Nat.add_le_add_left small _),?_,?_⟩⟩
  · intro B h
    obtain ⟨x,_,rfl⟩ := mem_image.mp h
    obtain ⟨block,_,root,off⟩ := spec x
    exact mem_sdiff.mpr ⟨block,fun h => (mem_union.mp h).elim (fun m => root (mem_filter.mp m).2) off⟩
  · intro i ne
    let x : U := ⟨i,mem_erase.mpr ⟨ne,mem_univ _⟩⟩
    exact ⟨mark x,mem_image_of_mem _ (mem_univ _),(spec x).2.1⟩
  · calc
      F.card ≤ (univ : Finset U).card := card_image_le
      _ = 2^(d+2)-1 := by simp [U,count]
  · intro t zero
    exact det t (fun B h => zero B (mem_union_right _ h))

abbrev interior {d : ℕ} {hd : 6≤d} (L : Layout d hd) := (cubeRule (d+2)).blocks \ L.exterior

theorem interior_size {d : ℕ} {hd : 6≤d} (L : Layout d hd) (B) (h : B∈interior L) : B.card=4 :=
  (((cubeRule (d+2)).mem_blocks B).mp (mem_sdiff.mp h).1).1

def blockOrder {d : ℕ} {hd : 6≤d} (L : Layout d hd) (B : interior L) : Symbol ≃ B.val :=
  (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe,interior_size L _ B.prop])).symm

#print axioms Layout
#print axioms layout_exists
#print axioms interior
#print axioms interior_size
#print axioms blockOrder
end
end Erdos722.AffineStar
