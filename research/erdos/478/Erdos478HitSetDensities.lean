import Erdos478GapObservableLaw
import Erdos478SieveProportions

/-! # Natural density and fair-coin bounds for factorial gap hit sets -/

namespace Erdos478.ConditionalGaps
open Finset FrobeniusCounts BinaryGap GapDensity RootMoments Filter Topology
open scoped Classical
noncomputable section

def law (s : Finset Nat.Primes) (E : Finset Nat.Primes → Prop) : ℝ :=
  uniform (Aut (CommonField s)) (fun g => if E (hits (CommonField s) s g) then 1 else 0)

def fairShare (s : Finset Nat.Primes) (E : Finset Nat.Primes → Prop) : ℝ :=
  ((s.powerset.filter E).card : ℝ)/2^s.card

theorem fair_event (s : Finset Nat.Primes) (E : Finset Nat.Primes → Prop) :
    fair s (fun u => if E u then 1 else 0)=fairShare s E := by
  unfold fair fairShare
  rw [card_filter,Nat.cast_sum]
  congr 1
  exact sum_congr rfl fun u _ => by by_cases h : E u <;> simp [h]

theorem increasing_lower (s : Finset Nat.Primes) (good : ∀ i∈s, broad i.val ∧ 3 < i.val)
    (E : Finset Nat.Primes → Prop) (inc : Monotone E) : fairShare s E≤law s E := by
  let : Normal ℚ (CommonField s) := Polynomial.SplittingField.instNormal (familyPoly s)
  rw [← fair_event]
  apply dominates (CommonField s) s good (fun _ hi => common_splits hi)
  intro u v huv
  by_cases h : E u
  · simp [h,inc huv h]
  · by_cases h' : E v <;> simp [h,h']

theorem decreasing_upper (s : Finset Nat.Primes) (good : ∀ i∈s, broad i.val ∧ 3 < i.val)
    (E : Finset Nat.Primes → Prop) (dec : Antitone E) : law s E≤fairShare s E := by
  classical
  let : Normal ℚ (CommonField s) := Polynomial.SplittingField.instNormal (familyPoly s)
  let f (u : Finset Nat.Primes) : ℝ := if E u then 1 else 0
  have inc : Monotone (-f) := by
    intro a b hab
    change -f a≤ -f b
    apply neg_le_neg
    by_cases h : E b
    · simp [f,h,dec hab h]
    · simp only [f,if_neg h]; split_ifs <;> norm_num
  have h := dominates (CommonField s) s good (fun _ hi => common_splits hi) _ inc
  have eq : fair s (-f)= -fair s f := by simp [fair,neg_div]
  rw [eq] at h
  change -fair s f≤uniform (Aut (CommonField s)) (-(fun g => f (hits (CommonField s) s g))) at h
  rw [map_neg,neg_le_neg_iff] at h
  exact h.trans_eq (fair_event s E)

theorem law_of_pit (pit : DegreeOnePrimeIdealTheorem) (s : Finset Nat.Primes) (E : Finset Nat.Primes → Prop) :
    Tendsto (fun X => GapSieve.fraction X (fun p => E (GapSieve.hits s p))) atTop (𝓝 (law s E)) := by
  have h := hit_score_mean (countingAverage pit) s (fun u => if E u then (1:ℝ) else 0)
  apply h.congr
  intro X
  exact GapSieve.ordinary_eq X _

/-- Probability that at least t of n independent fair coins are heads. -/
def binomialTail (n t : ℕ) : ℝ :=
  (∑ j∈range (n+1), if t≤j then (n.choose j : ℝ) else 0)/2^n

theorem count_lower (s : Finset Nat.Primes) (good : ∀ i∈s, broad i.val ∧ 3 < i.val) (t : ℕ) :
    binomialTail s.card t≤law s (fun u => t≤u.card) := by
  apply le_trans _ (increasing_lower s good _ (fun _ _ h ht => ht.trans (card_le_card h)))
  rw [← fair_event]
  unfold binomialTail fair
  dsimp only
  have sums := sum_powerset_apply_card (x:=s) (fun j => @ite ℝ (t≤j) (Classical.propDecidable _) 1 0)
  rw [sums]
  apply le_of_eq
  congr 1
  exact sum_congr rfl fun j _ => by split_ifs <;> simp_all

theorem all_hit_lower (s : Finset Nat.Primes) (good : ∀ i∈s, broad i.val ∧ 3 < i.val) :
    (2:ℝ)⁻¹^s.card≤law s (fun u => s⊆u) := by
  have h := increasing_lower s good (fun u => s⊆u) (fun _ _ hab hs => hs.trans hab)
  have eq : @Finset.filter _ (fun u => s⊆u) (fun u => Classical.propDecidable _) s.powerset={s} := by
    ext u
    simp only [mem_filter,mem_powerset,mem_singleton]
    exact ⟨fun h => Subset.antisymm h.1 h.2,fun e => e ▸ ⟨Subset.rfl,Subset.rfl⟩⟩
  unfold fairShare at h
  erw [eq] at h
  simpa [one_div] using h

theorem no_hit_upper (s : Finset Nat.Primes) (good : ∀ i∈s, broad i.val ∧ 3 < i.val) :
    law s (fun u => u=∅)≤(2:ℝ)⁻¹^s.card := by
  have h := decreasing_upper s good (fun u => u=∅) (fun _ _ hab he => Finset.subset_empty.mp (he ▸ hab))
  have eq : @Finset.filter _ (fun u => u=∅) (fun u => Classical.propDecidable _) s.powerset={∅} := by
    ext u
    simp only [mem_filter,mem_powerset,mem_singleton]
    exact ⟨And.right,fun e => ⟨e ▸ empty_subset _,e⟩⟩
  unfold fairShare at h
  erw [eq] at h
  simpa [one_div] using h

#print axioms law
#print axioms fairShare
#print axioms fair_event
#print axioms increasing_lower
#print axioms decreasing_upper
#print axioms law_of_pit
#print axioms binomialTail
#print axioms count_lower
#print axioms all_hit_lower
#print axioms no_hit_upper
end
end Erdos478.ConditionalGaps
