import Green51MarkedSpanRank

/-! # The intrinsic span of within-row differences -/
namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold
open scoped Classical

variable {I H : Type*} [AddCommGroup H] [Module F H]

def rowDirectionSpace (A : I → Finset H) : Submodule F H :=
  Submodule.span F {z | ∃ i x y,x∈A i ∧ y∈A i ∧ z=x-y}

theorem span_of_row_cores {J : Type*} (A : I → Finset H) (row : J → I) (v : J → H)
    (sites : ∀ i x,x∈rowCore (A i) ↔ ∃ j,row j=i ∧ v j=x) :
    Submodule.span F (Set.range v)=rowDirectionSpace A := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    have mem := (sites (row j) (v j)).mpr ⟨j,rfl,rfl⟩
    obtain ⟨x,hx,eq⟩ := mem_image.mp mem
    have live := (mem_erase.mp hx).2
    apply Submodule.subset_span
    exact ⟨row j,x,rowOrigin (A (row j)),live,rowOrigin_mem _ ⟨x,live⟩,eq.symm⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,x,y,hx,hy,rfl⟩
    have anchor {z : H} (hz : z∈A i) : z-rowOrigin (A i)∈Submodule.span F (Set.range v) := by
      by_cases eq : z=rowOrigin (A i)
      · rw [eq,sub_self]
        exact Submodule.zero_mem _
      · have core : z-rowOrigin (A i)∈rowCore (A i) :=
          mem_image.mpr ⟨z,mem_erase.mpr ⟨eq,hz⟩,rfl⟩
        obtain ⟨j,_,img⟩ := (sites i _).mp core
        exact Submodule.subset_span ⟨j,img⟩
    have diff := Submodule.sub_mem (Submodule.span F (Set.range v)) (anchor hx) (anchor hy)
    rw [sub_sub_sub_cancel_right] at diff
    exact diff

theorem intrinsic_rank_cap [Fintype I] [FiniteDimensional F H] (A : I → Finset H) :
    Module.finrank F (rowDirectionSpace A) + (occupiedRows A).card ≤ ∑ i,(A i).card := by
  classical
  let J := (i : I) × ↥(rowCore (A i))
  let row (j : J) : I := j.1
  let v (j : J) : H := j.2.val
  have sites (i : I) (x : H) : x∈rowCore (A i) ↔ ∃ j,row j=i ∧ v j=x := by
    constructor
    · intro hx
      exact ⟨⟨i,⟨x,hx⟩⟩,rfl,rfl⟩
    · rintro ⟨j,rfl,rfl⟩
      exact j.2.property
  have cap : Module.finrank F (rowDirectionSpace A) ≤ ∑ i,(rowCore (A i)).card := by
    rw [←span_of_row_cores A row v sites,←Finsupp.range_linearCombination]
    have t := LinearMap.finrank_range_le (Finsupp.linearCombination F v)
    simpa [J,Fintype.card_sigma] using t
  have occ : (occupiedRows A).card = ∑ i,if (A i).Nonempty then 1 else 0 := by
    exact Finset.card_filter _ _
  rw [occ]
  calc
    _ ≤ (∑ i,(rowCore (A i)).card)+∑ i,(if (A i).Nonempty then 1 else 0) :=
      Nat.add_le_add_right cap _
    _ = _ := by
      rw [←sum_add_distrib]
      exact sum_congr rfl fun i _ => core_occupancy _

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.intrinsic_rank_cap
#print axioms Green51FrameIsomorphisms.span_of_row_cores
