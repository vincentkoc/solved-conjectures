import Erdos478ManyEvenWitnesses
import Erdos478EvenGapDeficit

/-!
# Simultaneous witnesses below every large cutoff

For a fixed divisor `d`, use a count parameter exponential in `n/d`.
Between two successive ceilings the same set of witness primes remains
available. The next ceiling controls the double logarithm of the cutoff.
-/

namespace Erdos478.EffectiveResolvent
open Finset Real

def abundanceCeiling (n d : ℕ) :=
  2^((2*n+4)^(2*n+19)*2^(2*(n/d)+2))

private theorem ceiling_majorant (n d : ℕ) :
    witnessCeiling n (2^(n/d)) ≤ abundanceCeiling n d := by
  let b := 2*n+4
  let q := n/d
  have hs : 2^q+1 ≤ (2:ℕ)^(q+1) := by
    rw [pow_succ]
    have := Nat.one_le_pow q 2 (by decide)
    omega
  apply Nat.pow_le_pow_right (by decide)
  change b^19*(b^n)^2*(2^q+1)^2 ≤ b^(2*n+19)*2^(2*q+2)
  calc
    _ ≤ b^19*(b^n)^2*((2:ℕ)^(q+1))^2 := by gcongr
    _ = _ := by rw [← pow_mul,← pow_add,← pow_mul]; congr 2 <;> omega

private theorem index_lt (n d : ℕ) : n < abundanceCeiling n d := by
  have h₁ : n ≤ (2*n+4)^(2*n+19) :=
    (show n≤2*n+4 by omega).trans (Nat.le_self_pow (by omega) _)
  have h₂ : 1 ≤ (2:ℕ)^(2*(n/d)+2) := Nat.one_le_pow _ _ (by decide)
  exact (h₁.trans (by simpa using Nat.mul_le_mul_left ((2*n+4)^(2*n+19)) h₂)).trans_lt Nat.lt_two_pow_self

theorem bracket {X N d : ℕ} (h : abundanceCeiling N d ≤ X) :
    ∃ n, N≤n ∧ abundanceCeiling n d ≤ X ∧ X < abundanceCeiling (n+1) d := by
  let P := fun k => abundanceCeiling k d ≤ X
  let n := Nat.findGreatest P X
  have hNX := (index_lt N d).le.trans h
  have hn : P n := Nat.findGreatest_spec hNX h
  refine ⟨n,Nat.le_findGreatest hNX h,hn,?_⟩
  have hnext : n+1 ≤ X := (index_lt n d).trans_le hn
  exact lt_of_not_ge (Nat.findGreatest_is_greatest (P := P) (show n<n+1 by omega) hnext)

open scoped Classical in
theorem count_at_cutoff {X n d : ℕ} (hn : 0<n) (h : abundanceCeiling n d ≤ X) :
    2^(2^(n/d)) < ((range (X+1)).filter (EvenGapWitness n)).card := by
  apply (many_even_witnesses n (2^(n/d)) hn).trans_le
  apply card_le_card
  exact filter_subset_filter _ (range_mono (Nat.add_le_add_right ((ceiling_majorant n d).trans h) 1))

theorem loglog_successor {X n d : ℕ} (hX : 1<X) (h : X ≤ abundanceCeiling (n+1) d) :
    log (log X) ≤ (2*(n:ℝ)+21)*log (2*n+6) + (2*(((n+1)/d:ℕ):ℝ)+2)*log 2 := by
  have hg := loglog_two_pow hX h
  unfold abundanceCeiling at h
  change log (log X) ≤ log (((2*(n+1)+4)^(2*(n+1)+19)*2^(2*((n+1)/d)+2) : ℕ) : ℝ) at hg
  push_cast at hg
  rw [log_mul (by positivity) (by positivity),log_pow,log_pow] at hg
  push_cast at hg
  convert hg using 1
  ring_nf

#print axioms bracket
#print axioms count_at_cutoff
#print axioms loglog_successor

end Erdos478.EffectiveResolvent
