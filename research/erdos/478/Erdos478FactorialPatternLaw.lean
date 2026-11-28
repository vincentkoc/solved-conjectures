import Erdos478GapPatternMeans
import Erdos478FactorialEndpointCounts
import Erdos478PrimeProportions

/-!
# Exact prime frequencies for factorial collision counts

A length is saturated when it gives its maximum number of distinct pairs
of factorial indices. Specifying the saturated and unsaturated lengths
gives a finite inclusion-exclusion formula in splitting-field degrees.
-/

namespace Erdos478.SplittingDensity
open Polynomial Finset Filter Topology RootMoments GapDensity
open scoped Classical
noncomputable section

def observed (m : ℕ) (S T : Finset ℕ) (p : ℕ) : Prop :=
  m ∣ p-1 ∧ (∀ k∈S, (endpoints k p).card=k) ∧
    (∀ k∈T, (endpoints k p).card<k) ∧
    ((Ico 1 p).image (fun j => j.factorial % p)).card + ∑ k∈S, k ≤ p-1

private theorem observed_iff (m : ℕ) (S T : Finset ℕ)
    (hS : ∀ k∈S, 2≤k) (hT : ∀ k∈T, 2≤k) :
    ∃ B, ∀ p>B, p.Prime → (observed m S T p ↔ pattern m S T p) := by
  let U := S∪T
  let f := GapFamilies.family ℤ S
  refine ⟨max (U.sup cutoff) (f.resultant f.derivative).natAbs,?_⟩
  intro p hp hpr
  let : Fact p.Prime := ⟨hpr⟩
  have hc (k) (hk:k∈U) : cutoff k<p := ((le_sup hk).trans (le_max_left ..)).trans_lt hp
  have hs (k) (hk:k∈S) := saturated_iff (hS k hk) (hc _ (mem_union_left _ hk))
  have ht (k) (hk:k∈T) := saturated_iff (hT k hk) (hc _ (mem_union_right _ hk))
  constructor
  · rintro ⟨hm,h₁,h₂,_⟩
    exact ⟨⟨hm,fun k hk => (hs k hk).mpr (h₁ k hk)⟩,
      fun k hk h => (Nat.ne_of_lt (h₂ k hk)) ((ht k hk).mp h)⟩
  · rintro ⟨⟨hm,h₁⟩,h₂⟩
    have hreps (k) (hk:k∈S) := (hs k hk).mp (h₁ k hk)
    refine ⟨hm,hreps,?_,?_⟩
    · intro k hk
      exact lt_of_le_of_ne (endpoint_bound (hT k hk) (hc _ (mem_union_right _ hk)))
        (fun he => h₂ k hk ((ht k hk).mpr he))
    · have h := GapFamilies.card_add_sum_gap_roots S hS (p:=p) ((le_max_right ..).trans_lt hp)
      have he : (∑ k∈S, (descPochhammer (ZMod p) k-1).roots.card)=∑ k∈S, k := by
        apply sum_congr rfl
        intro k hk
        have h' := endpoint_count (hS k hk) (hc _ (mem_union_left _ hk))
        simpa [gapPoly] using h'.symm.trans (hreps k hk)
      rwa [he] at h

/-- The same law holds for any of the prime averages with mean one
for degree-one prime ideals. -/
theorem factorial_pattern_mean (A : PrimeAverage) {m : ℕ} (hm : 0<m) (S T : Finset ℕ)
    (hS : ∀ k∈S, 2≤k) (hT : ∀ k∈T, 2≤k) :
    Tendsto (fun X => A.avg X (event (observed m S T))) atTop (𝓝 (patternDensity m S T)) := by
  obtain ⟨B,hB⟩ := observed_iff m S T hS hT
  have h := A.finite_change (a:=event (observed m S T)) (b:=event (pattern m S T)) B
    (fun p hp hpr => by simp only [event,hB p hp hpr])
  have hlim := pattern_mean A hm S T (fun k hk => lt_of_lt_of_le (by decide : 0<2) (hS k hk))
    (fun k hk => lt_of_lt_of_le (by decide : 0<2) (hT k hk))
  simpa only [sub_add_cancel,zero_add] using h.add hlim

theorem factorial_pattern_of_pit (pit : DegreeOnePrimeIdealTheorem) {m : ℕ} (hm : 0<m)
    (S T : Finset ℕ) (hS : ∀ k∈S, 2≤k) (hT : ∀ k∈T, 2≤k) :
    Tendsto (fun X => (((Nat.primesLE X).filter (observed m S T)).card : ℝ) /
      (Nat.primesLE X).card) atTop (𝓝 (patternDensity m S T)) := by
  apply (factorial_pattern_mean (countingAverage pit) hm S T hS hT).congr
  intro X
  change (Nat.primeCounting X : ℝ)⁻¹*(∑ p∈Nat.primesLE X, if observed m S T p then 1 else 0)=_
  rw [← Nat.primesLE_card_eq_primeCounting,div_eq_inv_mul]
  congr 1
  rw [card_filter]
  push_cast
  rfl

#print axioms factorial_pattern_mean
#print axioms factorial_pattern_of_pit
end
end Erdos478.SplittingDensity
