import ThetaFivePrimeMoment
import Mathlib.Algebra.Order.Chebyshev

/-! Count triples hitting a forbidden set using the ordinary five-prime moment. -/
namespace Arxiv.«2501.03234».ThetaTernaryVertexDeletion
open Finset ThetaTernaryDeletion ThetaTernaryPacking ThetaTernaryIncidence ThetaFivePrimeMoment

def lost (A E : Finset ℕ) (n : ℕ) :=
  (triples A A A n).filter (fun t => ¬Disjoint (vertices t) E)

theorem square (A E : Finset ℕ) (n : ℕ) :
    (lost A E n).card^2 ≤ E.card*(9*five A n) := by
  let U := E∩A
  let F := incident (triples A A A n)
  have hsub : lost A E n ⊆ U.biUnion F := by
    intro t ht
    obtain ⟨hh,hd⟩ := mem_filter.mp ht
    obtain ⟨v,hv,hE⟩ := not_disjoint_iff.mp hd
    obtain ⟨ha,hb,hc,_⟩ := mem.mp hh
    have hA : v∈A := by
      simp only [vertices,mem_insert,mem_singleton] at hv
      rcases hv with rfl|rfl|rfl;exact ha;exact hb;exact hc
    exact mem_biUnion.mpr ⟨v,mem_inter.mpr ⟨hE,hA⟩,mem_filter.mpr ⟨hh,hv⟩⟩
  have hm : ∑ v∈U,(F v).card^2 ≤ moment A n :=
    sum_le_sum_of_subset_of_nonneg inter_subset_right (by intros; positivity)
  have hsum : (lost A E n).card ≤ ∑ v∈U,(F v).card :=
    (card_le_card hsub).trans card_biUnion_le
  calc _ ≤ (∑ v∈U,(F v).card)^2 := Nat.pow_le_pow_left hsum _
       _ ≤ U.card*∑ v∈U,(F v).card^2 := sq_sum_le_card_mul_sum_sq
       _ ≤ E.card*(9*five A n) :=
         Nat.mul_le_mul (card_le_card inter_subset_left) (hm.trans (moment_le A n))

theorem survive (A E : Finset ℕ) (n : ℕ) :
    (triples A A A n).card ≤ (distinctTriples (A\E) n).card+(lost A E n).card+3*A.card := by
  have hs : distinctTriples A n ⊆ distinctTriples (A\E) n ∪ lost A E n := by
    intro t ht
    obtain ⟨hh,hneq⟩ := mem_filter.mp ht
    by_cases h : Disjoint (vertices t) E
    · obtain ⟨ha,hb,hc,hn⟩ := mem.mp hh
      have h₁ := disjoint_left.mp h (show t.1∈vertices t by simp [vertices])
      have h₂ := disjoint_left.mp h (show t.2.1∈vertices t by simp [vertices])
      have h₃ := disjoint_left.mp h (show t.2.2∈vertices t by simp [vertices])
      exact mem_union_left _ (mem_filter.mpr ⟨mem.mpr ⟨mem_sdiff.mpr ⟨ha,h₁⟩,
        mem_sdiff.mpr ⟨hb,h₂⟩,mem_sdiff.mpr ⟨hc,h₃⟩,hn⟩,hneq⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hh,h⟩)
  exact (diagonal A n).trans (Nat.add_le_add_right ((card_le_card hs).trans (card_union_le _ _)) _)

#print axioms square
#print axioms survive
end Arxiv.«2501.03234».ThetaTernaryVertexDeletion
