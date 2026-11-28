import Erdos478SieveProportions
import Mathlib.Data.Nat.Sqrt

/-! # A finite threshold for a pointwise growing factorial deficit

The cutoff at p looks ahead only through the prime of index π(p)^2.
This turns fixed-threshold density one into a single set of prime moduli. -/

namespace Erdos478.LowGapAction
open Finset Filter Topology MeanDeficit GapDensity GapSieve
noncomputable section

def belowCount (X k : ℕ) := ((Nat.primesLE X).filter fun p => deficit p<k).card

def eligibleThresholds (X : ℕ) :=
  (range (X+1)).filter fun k => (k+1)*belowCount X k≤Nat.primeCounting X

private theorem zero_eligible (X : ℕ) : 0∈eligibleThresholds X := by
  apply mem_filter.mpr
  exact ⟨mem_range.mpr (by omega),by simp [belowCount]⟩

/-- Largest k≤X for which no more than one prime in k+1 has deficit below k. -/
def observedThreshold (X : ℕ) :=
  (eligibleThresholds X).max' ⟨0,zero_eligible X⟩

theorem observed_bound (X : ℕ) :
    (observedThreshold X+1)*belowCount X (observedThreshold X)≤Nat.primeCounting X :=
  (mem_filter.mp ((eligibleThresholds X).max'_mem ⟨0,zero_eligible X⟩)).2

private theorem observed_ge {X k : ℕ} (le : k≤X)
    (h : (k+1)*belowCount X k≤Nat.primeCounting X) : k≤observedThreshold X :=
  Finset.le_max' _ k (mem_filter.mpr ⟨mem_range.mpr (by omega),h⟩)

def horizon (p : ℕ) := max p (Nat.nth Nat.Prime ((Nat.primeCounting p)^2))
def lookAhead (p : ℕ) := Icc p (horizon p)
private theorem self_mem (p : ℕ) : p∈lookAhead p := mem_Icc.mpr ⟨le_rfl,le_max_left ..⟩

/-- Minimum observed threshold over p≤Y≤horizon(p). The search interval is finite. -/
def rollingThreshold (p : ℕ) :=
  ((lookAhead p).image observedThreshold).min' ⟨_,mem_image_of_mem _ (self_mem p)⟩

theorem rolling_le {p X : ℕ} (h : X∈lookAhead p) : rollingThreshold p≤observedThreshold X :=
  Finset.min'_le _ _ (mem_image_of_mem _ h)

theorem observed_grows (pit : DegreeOnePrimeIdealTheorem) : Tendsto observedThreshold atTop atTop := by
  refine tendsto_atTop.mpr fun k => ?_
  have small : Tendsto (fun X => (belowCount X k:ℝ)/(Nat.primesLE X).card) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x:=(1:ℝ))).sub (natural_density_of_prime_ideal_theorem pit k)
    rw [sub_self] at h
    apply h.congr'
    filter_upwards [Nat.tendsto_primeCounting.eventually_gt_atTop 0] with X pos
    have total := card_filter_add_card_filter_not (s:=Nat.primesLE X) (fun p => k≤deficit p)
    simp only [not_le] at total
    have he : (Nat.primesLE X).card≠0 := by rw [Nat.primesLE_card_eq_primeCounting]; omega
    unfold belowCount
    field_simp
    have eq : (((Nat.primesLE X).filter (fun p => k≤deficit p)).card:ℝ)+
        ((Nat.primesLE X).filter (fun p => deficit p<k)).card=(Nat.primesLE X).card := by exact_mod_cast total
    linarith
  have pos : 0<(k:ℝ)+1 := by positivity
  filter_upwards [eventually_ge_atTop k,small.eventually_lt_const (one_div_pos.mpr pos),
    Nat.tendsto_primeCounting.eventually_gt_atTop 0] with X le h nx
  apply observed_ge le
  rw [Nat.primesLE_card_eq_primeCounting] at h
  have nx' : 0<(Nat.primeCounting X:ℝ) := by exact_mod_cast nx
  have e := (div_lt_div_iff₀ nx' pos).mp h
  exact_mod_cast (show ((k:ℝ)+1)*belowCount X k≤Nat.primeCounting X by linarith)

theorem threshold_grows (pit : DegreeOnePrimeIdealTheorem) : Tendsto rollingThreshold atTop atTop := by
  refine tendsto_atTop.mpr fun k => ?_
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((observed_grows pit).eventually_ge_atTop k)
  filter_upwards [eventually_ge_atTop N] with p hp
  let S := (lookAhead p).image observedThreshold
  have mem : rollingThreshold p∈S := S.min'_mem ⟨_,mem_image_of_mem _ (self_mem p)⟩
  obtain ⟨Y,hY,eq⟩ := mem_image.mp mem
  exact eq ▸ hN Y (hp.trans (mem_Icc.mp hY).1)

/-- Among primes ≤X, at most √π(X) are too early for their look-ahead to
contain X. Every other failure lies in the observed lower tail at X. -/
theorem rolling_exception_count (X : ℕ) :
    ((Nat.primesLE X).filter fun p => deficit p<rollingThreshold p).card≤
      (Nat.primeCounting X).sqrt+belowCount X (observedThreshold X) := by
  let m := Nat.primeCounting X
  let T := (Nat.primesLE X).filter fun p => deficit p<observedThreshold X
  let N := Nat.nth Nat.Prime m.sqrt
  have card : (Nat.primesLE (N-1)).card=m.sqrt := by
    simp only [Nat.primesLE_card_eq_primeCounting,Nat.primeCounting_sub_one,N,Nat.primeCounting'_nth_eq]
  have sub : ((Nat.primesLE X).filter fun p => deficit p<rollingThreshold p) ⊆ Nat.primesLE (N-1) ∪ T := by
    intro p hp
    obtain ⟨pm,low⟩ := mem_filter.mp hp
    obtain ⟨le,prime⟩ := Nat.mem_primesLE.mp pm
    by_cases reach : X≤horizon p
    · exact mem_union_right _ (mem_filter.mpr ⟨pm,low.trans_le (rolling_le (mem_Icc.mpr ⟨le,reach⟩))⟩)
    · have late : Nat.nth Nat.Prime ((Nat.primeCounting p)^2)<X+1 :=
        (le_max_right ..).trans_lt (by change horizon p<X+1; omega)
      have sq : (Nat.primeCounting p)^2<m := (Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).mpr late
      have bound : Nat.primeCounting p≤m.sqrt := Nat.le_sqrt'.mpr sq.le
      have early : p+1≤N := (Nat.count_le_iff_le_nth Nat.infinite_setOfPred_prime).mp bound
      exact mem_union_left _ (Nat.mem_primesLE.mpr ⟨by omega,prime⟩)
  exact (card_le_card sub).trans ((card_union_le _ _).trans_eq (congrArg (·+T.card) card))

#print axioms belowCount
#print axioms eligibleThresholds
#print axioms observedThreshold
#print axioms observed_bound
#print axioms horizon
#print axioms lookAhead
#print axioms rollingThreshold
#print axioms rolling_le
#print axioms observed_grows
#print axioms threshold_grows
#print axioms rolling_exception_count
end
end Erdos478.LowGapAction
