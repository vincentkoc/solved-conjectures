import ThetaShortProgressions

/-! Count starting positions of uninterrupted runs in the ordered list of primes. -/
namespace Arxiv.«2501.03234».ThetaPrimeRuns
open Finset Filter Real
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable _

/-- Starts of full runs of L successive elements of A avoiding bad. -/
def starts (A : Finset ℕ) (L : ℕ) (bad : ℕ → Prop) :=
  (range (A.card+1-L)).filter (fun i => ∀ j : Fin A.card, i≤(j:ℕ) → (j:ℕ) < i+L →
    ¬bad (A.orderEmbOfFin rfl j))

/-- One bad element invalidates at most L possible starts, and the right boundary
costs at most L. The rank order is the ordinary increasing order on A. -/
theorem deletion (A : Finset ℕ) (L : ℕ) (bad : ℕ → Prop) :
    A.card ≤ (starts A L bad).card+L*(A.filter bad).card+L := by
  classical
  let B := univ.filter (fun j : Fin A.card => bad (A.orderEmbOfFin rfl j))
  let U := (range L).biUnion (fun d => B.image (fun j : Fin A.card => (j:ℕ)-d))
  have hB : B.card≤(A.filter bad).card := by
    apply card_le_card_of_injOn (A.orderEmbOfFin rfl)
    · exact fun j hj => mem_filter.mpr ⟨orderEmbOfFin_mem _ _ _,(mem_filter.mp hj).2⟩
    · exact (A.orderEmbOfFin rfl).injective.injOn
  have hU : U.card≤L*B.card := calc
    _ ≤ ∑ d∈range L,(B.image (fun j : Fin A.card => (j:ℕ)-d)).card := card_biUnion_le
    _ ≤ ∑ _d∈range L,B.card := sum_le_sum (fun _ _ => card_image_le)
    _ = _ := by simp
  have hsub : range (A.card+1-L)⊆starts A L bad ∪ U := by
    intro i hi
    by_cases hg : i∈starts A L bad
    · exact mem_union_left _ hg
    · apply mem_union_right _
      have h : ¬∀ j : Fin A.card, i≤(j:ℕ) → (j:ℕ) < i+L → ¬bad (A.orderEmbOfFin rfl j) :=
        fun hh => hg (mem_filter.mpr ⟨hi,hh⟩)
      push Not at h
      obtain ⟨j,hij,hj,he⟩ := h
      exact mem_biUnion.mpr ⟨(j:ℕ)-i,mem_range.mpr (by omega),
        mem_image.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,he⟩,by omega⟩⟩
  have hh := (card_le_card hsub).trans (card_union_le ..)
  rw [card_range] at hh
  have hu := hU.trans (Nat.mul_le_mul_left L hB)
  omega

#print axioms deletion
end
end Arxiv.«2501.03234».ThetaPrimeRuns
