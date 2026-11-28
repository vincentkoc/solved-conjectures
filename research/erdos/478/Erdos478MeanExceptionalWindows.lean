import Erdos478WindowBoundaryRoots
import Erdos478IsolatedWindowCounts
import Erdos478SeparableRootMean

/-! # Exact limiting mean of the number of exceptional positive factorial windows -/

namespace Erdos478.WindowAverage
open Polynomial Finset Filter Topology RootMoments LocalSpacing
open scoped Classical
noncomputable section

theorem pair_count_mean (A : PrimeAverage) {H r s : ℕ} (rs : r<s) (sH : s≤H) :
    Tendsto (fun X => A.avg X (fun p => ((equalStarts p H r s).card:ℝ))) atTop (𝓝 (if r+1=s then 0 else 1)) := by
  by_cases adj : r+1=s
  · subst s
    rw [if_pos rfl]
    apply CollisionLaw.mean_of_change A (b:=0) 0
    · intro p _ hp
      simp [adjacent_starts_empty hp sH]
    · simp
  · rw [if_neg adj]
    let f := translatedGap ℤ s (s-r)
    apply CollisionLaw.mean_of_change A (b:=roots f) (boundaryBound H s (s-r))
    · intro p h hp
      change ((equalStarts p H r s).card:ℝ)=(Nat.card (RootPairs.solutions (translatedGap ℤ s (s-r)) (ZMod p)):ℝ)
      exact_mod_cast equalStarts_exact hp (by omega : r+2≤s) sH h
    · apply first_mean A f (translated_degree ℤ s (by omega : 0<s-r)).monic
      change Irreducible ((translatedGap ℤ s (s-r)).map (Int.castRingHom ℚ))
      rw [map_translated]
      exact translated_irreducible s (by omega)

private theorem eligible_pairs (H : ℕ) :
    ∑ s ∈ range (H+1), ∑ r ∈ range s,(if r+1=s then (0:ℝ) else 1)=(H.choose 2:ℕ) := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [sum_range_succ,ih,sum_range_succ]
    have eq : (∑ r ∈ range H,(if r+1=H+1 then (0:ℝ) else 1))=H := by
      calc
        _=∑ _r ∈ range H,(1:ℝ) := sum_congr rfl fun r hr => if_neg (by have := mem_range.mp hr; omega)
        _=_ := by simp
    rw [eq,if_pos rfl,Nat.choose_succ_succ H 1,Nat.choose_one_right]
    push_cast
    ring

/-- A fixed span has exactly binom(H,2) exceptional starting positions on
average over primes, with the average taken before any variation in H. -/
theorem exceptional_count_mean (A : PrimeAverage) (H : ℕ) :
    Tendsto (fun X => A.avg X (fun p => ((exceptionalStarts p H 1).card:ℝ))) atTop (𝓝 (H.choose 2:ℕ)) := by
  let F : ℕ → ℝ := ∑ s ∈ range (H+1), ∑ r ∈ range s,(fun p : ℕ => ((equalStarts p H r s).card:ℝ))
  apply CollisionLaw.mean_of_change A (b:=F) ((H+2)^(H^2))
  · intro p large hp
    rw [isolated_count hp large,sum_pairEnergy]
    simp [F,Finset.sum_apply]
  · simp only [F,map_sum]
    rw [← eligible_pairs]
    exact tendsto_finsetSum _ fun s hs => tendsto_finsetSum _ fun r hr =>
      pair_count_mean A (mem_range.mp hr) (by have := mem_range.mp hs; omega)

#print axioms pair_count_mean
#print axioms exceptional_count_mean
end
end Erdos478.WindowAverage
