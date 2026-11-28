import Erdos478FiniteRootProfile
import Erdos478LowGapBezout

/-! # Modular witnesses for composite first collision lengths through ten -/

namespace Erdos478.LocalWitness
open Finset FirstCollision SplittingDensity GapDensity

/-- Test every residue and every strictly earlier eligible length. Blocks of
128 keep the depth of kernel reduction small for the larger sample moduli. -/
private def clearBlocks (p l : ℕ) : Bool :=
  (List.range (p/128+1)).all fun b => (List.range 128).all fun j =>
    (List.range (l-2)).all fun d => (128*b+j).descFactorial (d+2)%p != 1

private theorem earlier_empty {p l : ℕ} (clear : clearBlocks p l=true)
    (k : ℕ) (lo : 2≤k) (hi : k<l) : rawRoots p k=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨bound,hit⟩ := mem_filter.mp hx
  have lt := mem_range.mp bound
  have b : x/128∈List.range (p/128+1) := List.mem_range.mpr (by omega)
  have j : x%128∈List.range 128 := List.mem_range.mpr (by omega)
  have d : k-2∈List.range (l-2) := List.mem_range.mpr (by omega)
  have row := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp clear _ b) _ j) _ d
  change ((128*(x/128)+x%128).descFactorial (k-2+2)%p != 1)=true at row
  rw [Nat.div_add_mod,Nat.sub_add_cancel lo,hit] at row
  contradiction

private theorem sample {p l x : ℕ} (prime : Nat.Prime p) (lo : 2≤l) (hi : l≤10)
    (regular : ∀ k, 2≤k → k≤l → ¬p∣(lowCertificate k).1) (clear : clearBlocks p l=true)
    (bound : x<p) (hit : x.descFactorial l%p=1) (boundary : l.factorial%p≠1) :
    First p l ∧ ((∏ k∈Icc 2 l,k.factorial : ℕ) : ℝ)⁻¹≤firstDensity l := by
  let : Fact p.Prime := ⟨prime⟩
  have found : (rawRoots p l).Nonempty := ⟨x,mem_filter.mpr ⟨mem_range.mpr bound,hit⟩⟩
  refine ⟨⟨by omega,ConditionalGaps.hasGap_iff.mpr ?_,?_⟩,first_mass_of_sample p l lo
    (fun k hk hk' => low_gap_regular hk (hk'.trans hi) (regular k hk hk')) (earlier_empty clear) found⟩
  · have he := (rawRoots_card p l).trans (endpoint_correction l p)
    have hpos := card_pos.mpr found
    rw [he] at hpos
    simpa [boundary] using hpos
  · intro k pos small gap
    by_cases one : k=1
    · exact no_gap_one prime (one ▸ gap)
    have he := (rawRoots_card p k).trans (endpoint_correction k p)
    rw [earlier_empty clear k (by omega) small,card_empty] at he
    have := ConditionalGaps.hasGap_iff.mp gap
    omega

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

private theorem sample4 : First 47 4 ∧ ((∏ k∈Icc 2 4,k.factorial : ℕ) : ℝ)⁻¹≤firstDensity 4 := by
  apply sample (p:=47) (x:=15) (by norm_num) (by decide) (by decide)
  · intro k lo hi; interval_cases k <;> decide +kernel
  · decide +kernel
  · decide
  · decide +kernel
  · decide +kernel

private theorem sample6 : First 193 6 ∧ ((∏ k∈Icc 2 6,k.factorial : ℕ) : ℝ)⁻¹≤firstDensity 6 := by
  apply sample (p:=193) (x:=88) (by norm_num) (by decide) (by decide)
  · intro k lo hi; interval_cases k <;> decide +kernel
  · decide +kernel
  · decide
  · decide +kernel
  · decide +kernel

private theorem sample8 : First 5477 8 ∧ ((∏ k∈Icc 2 8,k.factorial : ℕ) : ℝ)⁻¹≤firstDensity 8 := by
  apply sample (p:=5477) (x:=2268) (by norm_num) (by decide) (by decide)
  · intro k lo hi; interval_cases k <;> decide +kernel
  · decide +kernel
  · decide
  · decide +kernel
  · decide +kernel

private theorem sample9 : First 1013 9 ∧ ((∏ k∈Icc 2 9,k.factorial : ℕ) : ℝ)⁻¹≤firstDensity 9 := by
  apply sample (p:=1013) (x:=316) (by norm_num) (by decide) (by decide)
  · intro k lo hi; interval_cases k <;> decide +kernel
  · decide +kernel
  · decide
  · decide +kernel
  · decide +kernel

private theorem sample10 : First 25117 10 ∧ ((∏ k∈Icc 2 10,k.factorial : ℕ) : ℝ)⁻¹≤firstDensity 10 := by
  apply sample (p:=25117) (x:=10336) (by norm_num) (by decide) (by decide)
  · intro k lo hi; interval_cases k <;> decide +kernel
  · decide +kernel
  · decide
  · decide +kernel
  · decide +kernel

/-- Each composite length through ten is the first positive factorial collision
distance on a set of primes of explicitly bounded ordinary density. -/
theorem small_composite_mass {l : ℕ} (hl : l∈({4,6,8,9,10}:Finset ℕ)) :
    ((∏ k∈Icc 2 l,k.factorial : ℕ) : ℝ)⁻¹≤firstDensity l := by
  simp only [mem_insert,mem_singleton] at hl
  rcases hl with rfl|rfl|rfl|rfl|rfl
  exacts [sample4.2,sample6.2,sample8.2,sample9.2,sample10.2]

theorem composite_first_samples : First 47 4 ∧ First 193 6 ∧ First 5477 8 ∧ First 1013 9 ∧ First 25117 10 :=
  ⟨sample4.1,sample6.1,sample8.1,sample9.1,sample10.1⟩

theorem through_eleven_pos (pit : DegreeOnePrimeIdealTheorem) {l : ℕ} (lo : 2≤l) (hi : l≤11) :
    0<firstDensity l := by
  by_cases prime : l.Prime
  · exact prime_atom_pos pit prime
  · have incl : l∈({4,6,8,9,10}:Finset ℕ) := by interval_cases l <;> first | decide | norm_num at prime
    exact lt_of_lt_of_le (by positivity) (small_composite_mass incl)

#print axioms composite_first_samples
#print axioms small_composite_mass
#print axioms through_eleven_pos
end Erdos478.LocalWitness
