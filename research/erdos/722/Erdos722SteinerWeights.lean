import Erdos722AllRankIndices
import FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite

/-!
# Nonnegative index one and the canonical Steiner predicate

A sum of natural block multiplicities equal to one gives exactly one block
of positive weight through each row. Signed weights at index one satisfy the
same divisibility tests, and may have negative entries.
-/

namespace Erdos722.IntegralDesign
open Finset Filter

theorem design_weights {α : Type*} [Fintype α] [DecidableEq α] {r k : ℕ}
    {H : Finset (Finset α)} (hH : H.IsBlockDesign r k) :
    Represents univ r k (fun _ => 1) (fun B => if B∈H then 1 else 0) := by
  intro A hA
  obtain ⟨B,⟨hB,hAB⟩,huniq⟩ := hH.2 A (mem_powersetCard.mp hA).2
  unfold incidence
  rw [sum_eq_single B,if_pos hB]
  · intro C hC hCB
    exact if_neg (fun h => hCB (huniq C ⟨h,(mem_filter.mp hC).2⟩))
  · intro h
    exact (h (mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,hH.1 B hB⟩,hAB⟩)).elim

theorem index_one_iff {α : Type*} [Fintype α] [DecidableEq α] (r k : ℕ) :
    Multiplicities (univ : Finset α) r k 1 ↔ ∃ H : Finset (Finset α), H.IsBlockDesign r k := by
  classical
  constructor
  · rintro ⟨w,hw⟩
    let blocks := (univ : Finset α).powersetCard k
    let H := blocks.filter (fun B => w B≠0)
    refine ⟨H,fun B hB => (mem_powersetCard.mp (mem_filter.mp hB).1).2,?_⟩
    intro A hA
    let U := blocks.filter (A⊆·)
    have sum : (∑ B∈U, w B)=1 := hw A (mem_powersetCard.mpr ⟨subset_univ _,hA⟩)
    obtain ⟨B,hB,hwB⟩ := exists_ne_zero_of_sum_ne_zero (sum.trans_ne (by decide))
    refine ⟨B,⟨mem_filter.mpr ⟨(mem_filter.mp hB).1,hwB⟩,(mem_filter.mp hB).2⟩,?_⟩
    rintro C ⟨hC,hAC⟩
    by_contra ne
    have hCU : C∈U := mem_filter.mpr ⟨(mem_filter.mp hC).1,hAC⟩
    have le : w C+w B≤∑ D∈U, w D := by
      calc
        _ = ∑ D∈({C,B} : Finset _), w D := by simp [ne]
        _ ≤ _ := sum_le_sum_of_subset (insert_subset hCU (singleton_subset_iff.mpr hB))
    have hwC := (mem_filter.mp hC).2
    omega
  · rintro ⟨H,hH⟩
    refine ⟨fun B => if B∈H then 1 else 0,fun A hA => ?_⟩
    have h := design_weights hH A hA
    change (∑ B∈(univ.powersetCard k).filter (A⊆·), if B∈H then (1:ℤ) else 0)=1 at h
    exact_mod_cast h

/-- The pinned divisibilities at index one characterize signed decompositions
at every parameter triple with r ≤ k ≤ n. -/
theorem signed_steiner_iff (n r k : ℕ) (hrk : r≤k) (hkn : k≤n) :
    (∃ w, Represents (univ : Finset (Fin n)) r k (fun _ => 1) w) ↔
      ∀ i<r, (k-i).choose (r-i) ∣ (n-i).choose (r-i) := by
  simpa [Conditions] using uniform_signed_iff (univ : Finset (Fin n)) hrk (by simpa using hkn) 1

/-- Below the square inclusion-matrix threshold, the complete design applied
with the admissible multiplicity gives the exact ordinary index-one answer. -/
theorem small_steiner_iff (n r k : ℕ) (hrk : r≤k) (hkn : k≤n) (hn : n≤k+r) :
    (∃ H : Finset (Finset (Fin n)), H.IsBlockDesign r k) ↔
      ∀ i<r, (k-i).choose (r-i) ∣ (n-i).choose (r-i) := by
  let V := (univ : Finset (Fin n))
  have hv : V.card=n := by simp [V]
  have he : Multiplicities V r k 1 ↔ Conditions V.card r k 1 := by
    refine ⟨conditions_of_multiplicities (by omega),fun h => ?_⟩
    exact multiples_realized V hrk ((small_order_period V hrk (by omega) (by omega)).mp h)
  simpa [V,Conditions] using (index_one_iff (α:=Fin n) r k).symm.trans he

/-- For fixed ranks, the remaining assertion in the pinned ordinary existence
statement is exactly eventual nonnegative realization of feasible signed rows. -/
theorem eventual_positivity_iff (r k : ℕ) (hrk : r≤k) :
    (∀ᶠ n : ℕ in Filter.atTop, (∀ i<r, (k-i).choose (r-i) ∣ (n-i).choose (r-i)) →
      ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign r k) ↔
    (∀ᶠ n : ℕ in Filter.atTop,
      (∃ w, Represents (univ : Finset (Fin n)) r k (fun _ => 1) w) →
      Multiplicities (univ : Finset (Fin n)) r k 1) := by
  constructor <;> intro H <;> filter_upwards [H,Filter.eventually_ge_atTop k] with n h hn
  · intro signed
    exact (index_one_iff r k).mpr (h ((signed_steiner_iff n r k hrk hn).mp signed))
  · intro div
    exact (index_one_iff r k).mp (h ((signed_steiner_iff n r k hrk hn).mpr div))

#print axioms eventual_positivity_iff
#print axioms index_one_iff
#print axioms signed_steiner_iff
#print axioms small_steiner_iff
end Erdos722.IntegralDesign
