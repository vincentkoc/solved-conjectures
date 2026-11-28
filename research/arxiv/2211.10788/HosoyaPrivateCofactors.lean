import HosoyaComplementaryFactors

/-! Almost all sampled sites simultaneously retain nearly their whole logarithmic
size in divisors whose primes occur nowhere else in the comparison window. -/

namespace Arxiv.«2211.10788».FactorMass

open Finset Filter Real HosoyaNeighbor
open scoped Topology Classical

/-- A divisor of size at least the specified logarithmic fraction, all of
whose prime factors exceed Y and do not occur at a distinct site within H. -/
def HasPrivateCofactor (s : HosoyaNeighbor) (n H Y : ℕ) (ε : ℝ) : Prop :=
  ∃ c : ℕ, c ∣ s.value n ∧ (1-ε)*log (s.value n) ≤ log c ∧
    ∀ p : ℕ, p.Prime → p ∣ c → Y < p ∧
      ∀ t m, s ≠ t ∨ n ≠ m → Nat.dist n m ≤ H → ¬ p ∣ t.value m

private def excluded (H Y : ℕ) := Y.primesLE ∪ (shiftDetProduct H).primeFactors

private theorem private_of_share {s : HosoyaNeighbor} {n H Y : ℕ} {ε : ℝ}
    (h : share (excluded H Y) (s.value n) ≤ ε) : HasPrivateCofactor s n H Y ε := by
  have nz : s.value n ≠ 0 := by
    intro hz
    have low := s.supportBounds.lower n
    rw [hz] at low
    simp at low
  refine ⟨cofactor (excluded H Y) (s.value n),cofactor_dvd _ nz,large_cofactor_of_share_le h,?_⟩
  intro p hp dv
  obtain ⟨mem,out⟩ := mem_sdiff.mp (prime_outside hp dv)
  constructor
  · by_contra! le
    exact out (mem_union_left _ (Nat.mem_primesLE.mpr ⟨le,hp⟩))
  · intro t m hd gap shared
    exact out (mem_union_right _ (Nat.mem_primeFactors.mpr
      ⟨hp,dvd_shiftDetProduct_of_shared hd gap (Nat.dvd_of_mem_primeFactors mem) shared,
        (shiftDetProduct_pos H).ne'⟩))

/-- For arbitrary moving progressions, both diagonals simultaneously have
a window-private divisor of logarithmic share at least 1-ε at density one. -/
theorem almost_all_private_cofactors (r d H Y : ℕ → ℕ) (hd : ∀ N, 0<d N)
    (hh : Tendsto (fun N : ℕ => (H N:ℝ)^2/(N*log N)) atTop (𝓝 0))
    (hy : Tendsto (fun N : ℕ => ((Y N).primeCounting:ℝ)/N) atTop (𝓝 0))
    {ε : ℝ} (ep : 0<ε) :
    Tendsto (fun N : ℕ => (Nat.count (fun i => ¬∀ s : HosoyaNeighbor,
      HasPrivateCofactor s (r N+d N*i) (H N) (Y N) ε) N:ℝ)/N) atTop (𝓝 0) := by
  let P (N : ℕ) := excluded (H N) (Y N)
  have sparse : Tendsto (fun N : ℕ => ((P N).card:ℝ)/N) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_
      (by simpa using hy.add (sparse_shift_primes H hh))
    apply Eventually.of_forall
    intro N
    rw [←add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (card_union_le ..).trans_eq (by rw [Nat.primesLE_card_eq_primeCounting])
  let x (s : HosoyaNeighbor) (N i : ℕ) := share (P N) (s.value (r N+d N*i))
  have mean (s : HosoyaNeighbor) : Tendsto (fun N : ℕ => (∑ i∈range N, x s N i)/(N:ℝ)) atTop (𝓝 0) :=
    sparse_mean_share s.supportBounds P r d hd sparse
  refine squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_
    (by simpa using ((mean .upper).add (mean .lower)).div_const ε)
  apply Eventually.of_forall
  intro N
  rw [←add_div,←sum_add_distrib,div_right_comm]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [le_div_iff₀ ep,Nat.count_eq_card_filter_range,←nsmul_eq_mul,←sum_const]
  rw [sum_filter]
  apply sum_le_sum
  intro i _
  split_ifs with bad
  · exact add_nonneg (share_bounds ..).1 (share_bounds ..).1
  · have ⟨s,hs⟩ := Classical.not_forall.mp bad
    have big : ε ≤ x s N i := le_of_lt (lt_of_not_ge (fun small => hs (private_of_share small)))
    cases s with
    | upper => exact big.trans (le_add_of_nonneg_right (share_bounds ..).1)
    | lower => exact big.trans (le_add_of_nonneg_left (share_bounds ..).1)

/-- Direct specialization to the exact upper sequence in the prime-values question,
including its initial value at index zero. -/
theorem canonical_sparse_mean_share (S : ℕ → Finset ℕ) (r d : ℕ → ℕ) (hd : ∀ N, 0<d N)
    (small : Tendsto (fun N : ℕ => ((S N).card:ℝ)/N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ i∈range N, share (S N) (lucasFibonacciSum (r N+d N*i)))/(N:ℝ))
      atTop (𝓝 0) :=
  sparse_mean_share upper_support_bounds S r d hd small

#print axioms canonical_sparse_mean_share
#print axioms almost_all_private_cofactors

end Arxiv.«2211.10788».FactorMass
