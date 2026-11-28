import Green51ShortenedFlatCounts

/-! # Intersections of completions through seventeen fixed labels -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions
open Green51ExtensionFibres Green51ShortenedCompletions
open scoped Classical Pointwise
namespace Green51SeventeenCompletions
local notation "V" => Cube 11

/-- Distinct 24-label completions agree on at most one point outside a fixed
seventeen-label set. Otherwise nineteen of their common points determine both. -/
theorem pair_meet {A B C : Finset V} (size : A.card = 17) (hb : B ∈ completions A)
    (hc : C ∈ completions A) (ne : B ≠ C) : ((B\A) ∩ (C\A)).card ≤ 1 := by
  classical
  obtain ⟨ab,bs,bgood⟩ := (mem_filter.mp hb).2
  obtain ⟨ac,cs,cgood⟩ := (mem_filter.mp hc).2
  by_contra! two
  obtain ⟨U,part,us⟩ := exists_subset_card_eq (show 2 ≤ ((B\A) ∩ (C\A)).card by omega)
  have dis : Disjoint A U := disjoint_left.mpr fun v ha hu => (mem_sdiff.mp (mem_inter.mp (part hu)).1).2 ha
  have sizeAU : (A ∪ U).card = 19 := by rw [card_union_of_disjoint dis,size,us]
  have withinB : A ∪ U ⊆ B := union_subset ab (part.trans (inter_subset_left.trans sdiff_subset))
  have withinC : A ∪ U ⊆ C := union_subset ac (part.trans (inter_subset_right.trans sdiff_subset))
  have avoids : ¬FlatAt (A ∪ U) 0 := fun h => bgood (Green51ElevenColumns.flat_mono withinB h)
  obtain ⟨D,_,only⟩ := unique_completion (by omega : 19 ≤ (A ∪ U).card) (by omega) avoids
  exact ne ((only B ⟨withinB,bs,bgood⟩).trans (only C ⟨withinC,cs,cgood⟩).symm)

/-- Thirteen possible next points force two distinct completions. -/
theorem two_of_thirteen {A : Finset V} (size : A.card = 17) (h : (holes A).card = 13) :
    (completions A).card = 2 := by
  classical
  have inside {B : Finset V} (hb : B ∈ completions A) : B\A ⊆ holes A := by
    intro v hv
    obtain ⟨ab,_,avoid⟩ := (mem_filter.mp hb).2
    obtain ⟨vb,va⟩ := mem_sdiff.mp hv
    exact mem_filter.mpr ⟨mem_univ _,va,fun f => avoid (Green51ElevenColumns.flat_mono (insert_subset vb ab) f)⟩
  have seven {B : Finset V} (hb : B ∈ completions A) : (B\A).card = 7 := by
    obtain ⟨ab,sz,_⟩ := (mem_filter.mp hb).2
    rw [card_sdiff_of_subset ab,sz,size]
  have cover (v : V) (hv : v ∈ holes A) : ∃ B ∈ completions A, v ∈ B\A := by
    obtain ⟨fresh,good⟩ := (mem_filter.mp hv).2
    have count := card_insert_of_notMem fresh
    have c := completion_count (by omega : 18 ≤ (insert v A).card) (by omega) good
    rw [if_pos (by omega)] at c
    obtain ⟨B,hB⟩ := card_pos.mp (show 0 < (completions (insert v A)).card by omega)
    obtain ⟨next,sz,avoid⟩ := (mem_filter.mp hB).2
    exact ⟨B,mem_filter.mpr ⟨mem_univ _,(subset_insert ..).trans next,sz,avoid⟩,
      mem_sdiff.mpr ⟨next (mem_insert_self ..),fresh⟩⟩
  have lower : 2 ≤ (completions A).card := by
    by_contra! few
    obtain ⟨x,hx⟩ := card_pos.mp (show 0 < (holes A).card by omega)
    obtain ⟨B,hB,_⟩ := cover x hx
    have all : holes A ⊆ B\A := by
      intro v hv
      obtain ⟨C,hC,insideC⟩ := cover v hv
      have eq : C=B := card_le_one.mp (by omega : (completions A).card ≤ 1) C hC B hB
      rwa [←eq]
    have cardBound := card_le_card all
    have sz := seven hB
    omega
  by_contra ne
  obtain ⟨T,sub,sz⟩ := exists_subset_card_eq (show 3 ≤ (completions A).card by omega)
  obtain ⟨B,C,D,bc,bd,cd,rfl⟩ := card_eq_three.mp sz
  have b : B ∈ completions A := sub (by simp)
  have c : C ∈ completions A := sub (by simp)
  have d : D ∈ completions A := sub (by simp)
  have u := card_union_add_card_inter (B\A) (C\A)
  have v := card_union_add_card_inter ((B\A) ∪ (C\A)) (D\A)
  rw [union_inter_distrib_right] at v
  have overlaps := card_union_le ((B\A) ∩ (D\A)) ((C\A) ∩ (D\A))
  have bound := card_le_card (union_subset (union_subset (inside b) (inside c)) (inside d))
  have m := pair_meet size b c bc
  have l := pair_meet size b d bd
  have r := pair_meet size c d cd
  have b7 := seven b
  have c7 := seven c
  have d7 := seven d
  omega
end Green51SeventeenCompletions
#print axioms Green51SeventeenCompletions.pair_meet
#print axioms Green51SeventeenCompletions.two_of_thirteen
