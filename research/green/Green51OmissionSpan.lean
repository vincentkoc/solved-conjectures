import Green51AffineFrameRows
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # A small common span for the omitted sites of a finite word -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold
open scoped Classical
variable {I H : Type*} [AddCommGroup H] [Module F H] [DecidableEq H]

/-- One origin in each occupied omission row saves one dimension of the common span. -/
theorem common_omission_span (B : Finset I) (holes : I → Finset H) :
    ∃ (P : Submodule F H) (origin : I → H),
      Module.finrank F P ≤ ∑ i∈B,((holes i).card-1) ∧
      ∀ i∈B, ∀ x∈holes i, x-origin i∈P := by
  classical
  let origin (i : I) : H := if hi : (holes i).Nonempty then hi.choose else 0
  have chosen (i : I) (hi : (holes i).Nonempty) : origin i ∈ holes i := by
    simpa only [origin,dif_pos hi] using hi.choose_spec
  let dirs (i : I) := ((holes i).erase (origin i)).image (fun x => x-origin i)
  let all := B.biUnion dirs
  let P := Submodule.span F (all : Set H)
  refine ⟨P,origin,?_,?_⟩
  · calc
      Module.finrank F P ≤ all.card := finrank_span_finset_le_card (R := F) all
      _ ≤ ∑ i∈B,(dirs i).card := card_biUnion_le
      _ ≤ ∑ i∈B,((holes i).card-1) := by
        apply sum_le_sum
        intro i hi
        by_cases h : (holes i).Nonempty
        · exact (card_image_le).trans (le_of_eq (card_erase_of_mem (chosen i h)))
        · have eq := not_nonempty_iff_eq_empty.mp h
          simp [dirs,eq]
  · intro i hi x hx
    by_cases eq : x=origin i
    · simp [eq]
    · exact Submodule.subset_span (mem_biUnion.mpr ⟨i,hi,mem_image.mpr ⟨x,mem_erase.mpr ⟨eq,hx⟩,rfl⟩⟩ :
        x - origin i∈all)

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.common_omission_span
