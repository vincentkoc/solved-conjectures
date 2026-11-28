import Erdos722TwoStemGeometry

/-!
# Blocks through a fixed pair

Removing two marked points from the blocks containing them partitions
the other points into groups. Coordinate the groups and their points,
then delete the blocks of the pencil to obtain the line-face filling.
-/

namespace Erdos722.TwoStem
open Finset Function PointedProduct
open scoped Classical
noncomputable section

private def both {Y : Type*} (B : Finset Y) := B.insertNone.insertNone

private theorem both_subset {Y : Type*} {A B : Finset Y} : both A⊆both B ↔ A⊆B :=
  insertNone.le_iff_le.trans insertNone.le_iff_le

private def row {U V : Type*} [Fintype U] [Fintype V] (x : U) : Finset (Space U V) :=
  both (univ.filter fun p : U × V => p.1=x)

private theorem sub_row {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U]
    {T : Finset (Space U V)} {x : U} : T⊆row x ↔ trace T⊆{x} := by
  constructor
  · intro h a ha
    obtain ⟨b,hb⟩ := mem_trace.mp ha
    have hr := h hb
    simpa [row,both] using hr
  · intro h z hz
    rcases z with _|(_|⟨a,b⟩)
    · exact none_mem_insertNone
    · exact some_mem_insertNone.mpr none_mem_insertNone
    · have ha := mem_singleton.mp (h (mem_trace.mpr ⟨b,hz⟩))
      simpa [row,both] using ha

private def delete_rows {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [Nonempty U]
    {k : ℕ} {D : Finset (Finset (Space U V))} (hD : D.IsBlockDesign 3 k)
    (rows : ∀ x : U, row x∈D) : Template k .line U V := by
  classical
  let keep (B : Finset (Space U V)) := ∀ x : U, B≠row x
  have eligible {T : Finset (Space U V)} : 2≤(trace T).card ↔ ∀ x : U, ¬T⊆row x := by
    simp only [sub_row,← not_exists,← card_le_one_iff_subset_singleton]
    omega
  refine ⟨D.filter keep,fun B h => hD.1 B (mem_filter.mp h).1,?_,?_⟩
  · intro B hB T hTB hc
    obtain ⟨hb,hkeep⟩ := mem_filter.mp hB
    exact eligible.mpr fun x hx => hkeep x ((hD.2 T hc).unique ⟨hb,hTB⟩ ⟨rows x,hx⟩)
  · intro T hc ha
    obtain ⟨B,⟨hb,hs⟩,hu⟩ := hD.2 T hc
    exact ⟨B,⟨mem_filter.mpr ⟨hb,fun x he => eligible.mp ha x (he ▸ hs)⟩,hs⟩,
      fun C hC => hu C ⟨(mem_filter.mp hC.1).1,hC.2⟩⟩

variable {Y : Type*} [Fintype Y] {H : Finset (Finset (Option (Option Y)))}

private def pencil (H : Finset (Finset (Option (Option Y)))) :=
  univ.filter fun B : Finset Y => both B∈H

private theorem pencil_mem (B : Finset Y) : B∈pencil H ↔ both B∈H := by simp [pencil]

private theorem pencil_partition {m : ℕ} (design : H.IsBlockDesign 3 (m+2)) (y : Y) :
    ∃! B : {B // B∈pencil H}, y∈B.val := by
  classical
  obtain ⟨C,⟨hc,hs⟩,hu⟩ := design.2 (both {y}) (by simp [both])
  have ho : none∈C := hs none_mem_insertNone
  have hi : none∈C.eraseNone := mem_eraseNone.mpr (hs (some_mem_insertNone.mpr none_mem_insertNone))
  have recov : both C.eraseNone.eraseNone=C := by
    simp [both,insert_eq_of_mem,hi,ho]
  let B : {B // B∈pencil H} := ⟨C.eraseNone.eraseNone,(pencil_mem _).mpr (recov.symm ▸ hc)⟩
  refine ⟨B,?_,?_⟩
  · exact singleton_subset_iff.mp (both_subset.mp (recov.symm ▸ hs))
  · intro A ha
    apply Subtype.ext
    have he := hu (both A.val) ⟨(pencil_mem _).mp A.prop,both_subset.mpr (singleton_subset_iff.mpr ha)⟩
    exact insertNone.injective (insertNone.injective (he.trans recov.symm))

/-- A design on d*m+2 points with block size m+2 supplies the line
filling on d groups of m, by deleting its blocks through a fixed pair. -/
def pencil_filling {d m : ℕ} [NeZero d] (hm : 0<m) (hY : Fintype.card Y=d*m)
    (design : H.IsBlockDesign 3 (m+2)) : Template (m+2) .line (Fin d) (Fin m) := by
  classical
  let J := {B // B∈pencil H}
  let group (y : Y) : J := (pencil_partition design y).choose
  have member (y : Y) (B : J) : group y=B ↔ y∈B.val := by
    constructor
    · rintro rfl
      exact (pencil_partition design y).choose_spec.1
    · exact fun h => ((pencil_partition design y).choose_spec.2 B h).symm
  have size (B : J) : B.val.card=m := by
    have h := design.1 _ ((pencil_mem _).mp B.prop)
    simpa [both,Nat.add_assoc] using h
  let label (B : J) := B.val.equivFinOfCardEq (size B)
  let E : Y ≃ J × Fin m := (Equiv.sigmaFiberEquiv group).symm.trans
    (Equiv.sigmaEquivProdOfEquiv fun B => (Equiv.subtypeEquivRight (fun y => member y B)).trans (label B))
  have cardJ : Fintype.card J=d := by
    have h := Fintype.card_congr E
    rw [hY,Fintype.card_prod,Fintype.card_fin] at h
    exact Nat.eq_of_mul_eq_mul_right hm h.symm
  let index := Fintype.equivFinOfCardEq cardJ
  let e := E.trans (index.prodCongr (Equiv.refl (Fin m)))
  let g := e.optionCongr.optionCongr
  apply delete_rows (relabel_design g design)
  intro x
  let B : J := index.symm x
  apply mem_image.mpr
  refine ⟨both B.val,(pencil_mem _).mp B.prop,?_⟩
  ext z
  rw [mem_map_equiv]
  rcases z with _|(_|⟨a,b⟩)
  · exact iff_of_true none_mem_insertNone none_mem_insertNone
  · exact iff_of_true (some_mem_insertNone.mpr none_mem_insertNone) (some_mem_insertNone.mpr none_mem_insertNone)
  · change some (some (e.symm (a,b)))∈both B.val ↔ some (some (a,b))∈row x
    simp only [both,row,some_mem_insertNone,mem_filter,mem_univ,true_and]
    rw [← member,← index.injective.eq_iff]
    change (e (e.symm (a,b))).1=index (index.symm x) ↔ a=x
    simp

#print axioms pencil_filling
end
end Erdos722.TwoStem
