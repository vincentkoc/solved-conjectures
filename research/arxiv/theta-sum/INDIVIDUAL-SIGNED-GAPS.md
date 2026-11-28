# Individual prime gaps with opposite theta-product biases

Write \(R(p)=S(p)/p-\tfrac12\log p\) for the residual of the original integer sum, \(B\) for its all-prime mean, and \(C>0\) for its modulo-three character coefficient. For \(1\le h\le H\) set
\[
 Z_X(h)=\frac{(\log X)^2}{X}\sum_{\substack{X<p\le2X\\p,\ p+h\ {\rm prime}}}
        (R(p)-B)(R(p+h)-B).
\]
Fix \(1/6<\theta\le1\). The following hold for all sufficiently large integers \(X\), simultaneously for every integer \(X^\theta\le H\le X\).

- For every \(0\le b<3C^2\), at least \(\eta_b H\) even displacements \(h\le H\) divisible by three satisfy \(Z_X(h)\ge b\).
- For each \(d=1,2\) and every \(0\le b<3C^2/2\), at least \(\eta_{b,d}H\) even displacements \(h\le H\) with \(h\equiv d\bmod3\) satisfy \(Z_X(h)\le-b\).

All density constants are positive and may depend on \(\theta\). In particular, taking any strictly positive threshold in the indicated range gives opposite signed excesses of order \(X/(\log X)^2\) at a positive proportion of individual gaps. These are products centered at the global residual mean. The qualifying displacements may change with \(X,H\). The thresholds are the means per compatible even displacement. [Original theorem and exact quantifiers](ThetaIndividualGapSigns.lean) · [Compatible shifts](ThetaCompatibleSignedGaps.lean) · [Unweighted gap means](NEARBY-PRIME-PAIRS.md) · [Euler product for C](EXACT-MOD-THREE-BIAS.md) · [Pinned DeepMind sum](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean)

## Kernel replay

Independent Lean 4.33.1 replay checked 262 modules, including the 242 notebook sources, the pinned DeepMind source, and the external prime-number theorem, the upper sieve and the documented bridges. All 760 distinct axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.

## From signed means to many individual displacements

Let \(n_h\) be the ordinary number of eligible pairs at lag \(h\), \(a_e\) their centered products, and \(v_h=\sum_{e\text{ at }h}a_e\). For every finite set \(I\) of displacements, two applications of Cauchy–Schwarz within each fiber and one across fibers give
\[
  \left(\sum_{h\in I}v_h^2\right)^2\le
   \left(\sum_{h\in I}n_h^3\right)
   \left(\sum_{h\in I}\sum_{e\text{ at }h}a_e^4\right).
\]
The pair-count upper sieve costs \(\prod_{p\mid h}(1+3/p)\). Its cube is bounded by \(\prod_{p\mid h}(1+64/p)\), whose mean on the range of lags is at most \(e^{64}\) up to the endpoint term. The global fourth moment of \(a_e\) is bounded after pair normalization by the joint polynomial-test theorem. Thus \(\sum_{h\le H,\,h\equiv d(3)} Z_X(h)^2\ll_\theta H\) uniformly along every admissible length schedule. [Finite fourth-moment inequality](ThetaLagMomentDispersion.lean) · [Ordinary sieve and squared lag scores](ThetaSignedGapEnergy.lean) · [Fourth moment on nearby pairs](ThetaGapFourthMoment.lean)

The signed first moments divided by \(H\) tend respectively to \(C^2/2,-C^2/4,-C^2/4\). Every contributing gap is even for \(X\ge2\); at most \(H/6+1\) displacements in one residue class can contribute. Subtract a fixed threshold from the suitably signed score on these compatible gaps. Strict inequality at the threshold leaves a positive first-moment surplus proportional to \(H\). Cauchy–Schwarz and the second-moment bound put a positive fraction of displacements above threshold. Choosing a bad length at each failing endpoint gives the simultaneous conclusion. [Gap grouping and injection into ordinary prime pairs](ThetaGapFibres.lean) · [Uniformity in the length](ThetaFrequentSignedGaps.lean)

## Analytic inputs and comparison

The documented theorem below retains one ordinary-prime input. Koukoulopoulos's Theorem 1.2 gives the required almost-all short-interval counts in fixed reduced classes for exponents strictly above \(1/6\). The conversion to the unweighted per-length hypothesis appears in the almost-all window note. Lemma 4 of Funkhouser, Goldston, Sengupta and Sengupta bounds the number of prime pairs at each positive even displacement. For odd displacement at most one pair contains two primes. The pinned PNT and OMA upper-sieve bridges discharge the fixed-modulus global prime theorem and the prime-pair upper bound below. [Exact OMA comparison](PRIME-PAIR-SIEVE.md) [Koukoulopoulos](https://arxiv.org/pdf/1405.6592#page=3) · [Per-length input](ALMOST-ALL-PRIME-WINDOWS.md) · [Prime Difference Champions, Lemma 4](https://arxiv.org/pdf/1612.02938#page=16) · [Upper-sieve normalization](LOGARITHMIC-PRIME-GAPS.md)

The DeepMind issue treats pointwise bounds on a common remainder. OMA's finite-range certificate and the independent Hardy-sum identity address pointwise evaluations. The signed lag averages here concern the original aggregate over distinct pairs of primes. Pointwise positivity at every odd prime remains open. [Original paper](https://arxiv.org/abs/2501.03234) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA finite bound](https://github.com/lefttosolve2/open-math-agents/pull/34398) · [Independent partial](https://github.com/umaia1234/agentic-conjectures/pull/65) · [LTS target](https://lefttosolve.com/p/Arxiv.2501.03234.conjecture_4_2.R1.H1)

```lean
import ThetaIndividualGapSigns
import ThetaPNTCorollaries
import ThetaPairSieveComparison

/-! Pinned external bridges supply the ordinary global PNT and the prime-pair upper sieve. -/
namespace Arxiv.«2501.03234».ThetaIndividualGapSignsPNT
open ThetaAlmostPrimeDistribution ThetaPopularLagCounts ThetaPNTCorollaries

theorem original (h : DistributionInput) {θ : ℝ} (hθ : 1/6<θ) (ht : θ≤1) :
    ThetaIndividualGapSigns.Statement θ :=
  ThetaIndividualGapSigns.original h progression_mangoldt ThetaPairSieveComparison.original hθ ht

#print axioms original
end Arxiv.«2501.03234».ThetaIndividualGapSignsPNT
```

Codex assisted with the derivation and Lean formalization.
