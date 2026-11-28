# Uniform upper sieve for prime pairs

For some absolute \(C>0\), every sufficiently large \(X\) and every \(1\le h\le X\),
\[
 \#\{p:p,\ p+h\le X\text{ both prime}\}\,(\log X)^2
 \le C X\prod_{\ell\mid h,\ \ell\ {\rm prime}}(1+3/\ell).
\]
Both endpoints are ordinary unweighted primes. For positive even \(h\), the elementary Selberg sieve proved in the OMA Romanoff development counts every starting prime \(p\le X\), including those with \(p+h>X\). Its factor over odd prime divisors of \(h\) is \(\prod_{\ell\mid h,\ell>2}(1+1/\ell)\). Each factor can be enlarged to the displayed weight. For odd \(h\), the only possible starting prime is two. [Original sieve and proof](https://github.com/lefttosolve2/open-math-agents/blob/5fcc6d0d86261f3e086a24f7cc532cc83ba88629/proofs/Erdos16.erdos_16.variant.romanoff.R1.H2.lean#L1868-L1878) · [Notebook predicate and application](ThetaPopularLagCounts.lean)

Use lines 2 through 1878 inclusive of the pinned OMA file as `ThetaExternalPairSieve.lean`. This retains the source comments, Mathlib import and complete Mertens and Selberg sieve developments up to `OMALib.Sieve.prime_pairs_upper_bound'`. Line one imports the unrelated Romanoff reduction. The source Git blob is `8f5e4067bf9ec426800f3b6b415cda4231c74e49`. The following module is `ThetaPairSieveComparison`.

```lean
import ThetaPopularLagCounts
import ThetaExternalPairSieve

/-! The pinned OMA Romanoff prime-pair sieve supplies the uniform finite-lag estimate. -/
namespace Arxiv.«2501.03234».ThetaPairSieveComparison
open Finset Filter Real ThetaPopularLagCounts ThetaLagSieveWeights ThetaDistinctPrimeQuadruples
open scoped Topology

private theorem log_bound : ∀ᶠ X : ℕ in atTop,(log X)^2≤(X:ℝ) := by
  have h := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ)<1)).bound (by norm_num : (0:ℝ)<1))
  filter_upwards [h] with X hx
  simpa only [rpow_two,rpow_one,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (log (X:ℝ))),abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) X),one_mul] using hx

theorem original : Upper := by
  obtain ⟨C,hC,H⟩ := OMALib.Sieve.prime_pairs_upper_bound'
  refine ⟨max 1 C,lt_of_lt_of_le zero_lt_one (le_max_left ..),?_⟩
  filter_upwards [log_bound,eventually_ge_atTop 2] with X hslow hX h hh _
  have hw : 1≤weight 3 h := Finset.one_le_prod (fun p _ => by change 1≤1+3/(p:ℝ);linarith only [show 0≤3/(p:ℝ) by positivity])
  by_cases he : Even h
  · have hsub : pairs X h⊆(range (X+1)).filter (fun p => p.Prime ∧ (p+h).Prime) := by
      intro p hp;obtain ⟨h₁,h₂⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨mem_range.mpr (by have := (Nat.mem_primesLE.mp h₁).1;omega),(Nat.mem_primesLE.mp h₁).2,(Nat.mem_primesLE.mp h₂).2⟩
    have hwt : OMALib.Sieve.pairSingularProduct h≤weight 3 h := by
      unfold OMALib.Sieve.pairSingularProduct weight
      calc _ ≤ ∏ p∈h.primeFactors.filter (2<·),(1+3/(p:ℝ)) := by
               apply Finset.prod_le_prod (fun p _ => by positivity) (fun p _ => by gcongr;norm_num)
           _ ≤ _ := Finset.prod_le_prod_of_subset_of_one_le (filter_subset _ _)
               (fun p _ => by positivity) (fun p _ _ => by linarith only [show 0≤3/(p:ℝ) by positivity])
    have hb := (show ((pairs X h).card:ℝ)≤(((range (X+1)).filter (fun p => p.Prime ∧ (p+h).Prime)).card:ℝ) by exact_mod_cast card_le_card hsub).trans (H h hh he X hX)
    have hl : 0<(log X)^2 := sq_pos_of_pos (log_pos (by exact_mod_cast (show 1<X by omega)))
    have hb' : ((pairs X h).card:ℝ)≤(C*X*OMALib.Sieve.pairSingularProduct h)/(log X)^2 := hb.trans_eq (by ring)
    apply ((le_div_iff₀ hl).mp hb').trans
    exact mul_le_mul (mul_le_mul_of_nonneg_right (le_max_right 1 C) (Nat.cast_nonneg X)) hwt
      (le_trans (by norm_num) (OMALib.Sieve.one_le_pairSingularProduct h)) (by positivity)
  · have hs : pairs X h⊆{2} := by
      intro p hp;obtain ⟨h₁,h₂⟩ := mem_filter.mp hp;have pp := (Nat.mem_primesLE.mp h₁).2
      have pr := (Nat.mem_primesLE.mp h₂).2
      rcases pp.eq_two_or_odd with rfl|hodd
      · simp
      · have ho := Nat.not_even_iff_odd.mp he
        have heven := (Nat.odd_iff.mpr hodd).add_odd ho
        have : p+h=2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two pr).mp (even_iff_two_dvd.mp heven) |>.symm
        have := pp.two_le;omega
    have hc : ((pairs X h).card:ℝ)≤1 := by exact_mod_cast (card_le_card hs).trans_eq (card_singleton 2)
    apply (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans
    rw [one_mul]
    apply hslow.trans
    calc (X:ℝ)=1*X*1 := by ring
         _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left 1 C) (Nat.cast_nonneg X)) hw zero_le_one (by positivity)

#print axioms original
end Arxiv.«2501.03234».ThetaPairSieveComparison
```
