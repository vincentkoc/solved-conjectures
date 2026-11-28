# Nearby prime pairs and the theta residual

Let \(R(p)=S(p)/p-\tfrac12\log p\) for the original signed arithmetic sum. Give equal weight to each directed pair
\[
 X<p\le 2X,\qquad p<r\le p+H,\qquad p,r\text{ prime}.
\]
For every \(1/6<\theta\le1\) and every length schedule \(X^\theta\le H=H(X)\le X\) eventually, the empirical distribution of \((R(p),R(r))\) converges weakly on \(\mathbb R^2\) to \(\mu\otimes\mu\), where \(\mu\) is the one-prime Haar pushforward. The number of pairs is asymptotic to \(XH/(\log X)^2\). This allows every bounded continuous joint test, including tests that do not factor. The pairs range over all positive gaps through \(H\). The proof gives no assertion about any one fixed gap. [Joint weak law and pair count](ThetaNearbyResidualLaw.lean) · [Unweighted empirical measure](ThetaPairEmpirical.lean) · [Original one-prime law](PRIME-RESIDUAL-LAW.md) · [Pinned arithmetic sum](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean)

Prescribe independent fixed reduced classes \(a\bmod q\) and \(b\bmod s\) for the first and second primes. Their pair count is asymptotic to \(XH/(\varphi(q)\varphi(s)(\log X)^2)\), even when the moduli share factors. Giving each eligible pair equal mass yields the product of the two individual conditional Haar laws. Thus the limiting law factors after both class conditions are imposed. In particular both primes may be required to be \(1\bmod8\) and retain the same product law as unrestricted primes. [Class pair theorem](ThetaClassPairLaws.lean) · [Class-masked test limits](ThetaClassPairProducts.lean) · [One-prime conditional laws](SHORT-RESIDUAL-LAW.md)

**The sign of the mean product depends on the gap modulo three.** Let \(B\) be the all-prime mean of \(R\), and let \(C>0\) be the Euler product in the exact modulo-three bias theorem. Give equal weight to the pairs with prescribed gap residue \(r-p\equiv d\bmod 3\), still allowing all positive gaps through \(H\). The mean of
\[
   (R(p)-B)(R(r)-B)
\]
tends to \(+C^2\) for \(d=0\) and to \(-C^2\) for each of \(d=1,2\). The three pair counts are respectively asymptotic to \(1/2,1/4,1/4\) times \(XH/(\log X)^2\). The result holds on every admissible length schedule with \(\theta>1/6\). The centering constant is the common all-prime mean. For \(d=1\), only the ordered endpoint classes \(1,2\bmod3\) occur, with centered means \(C,-C\). For \(d=2\) they occur in reverse order. For \(d=0\) the two same-class contributions have the same positive product. [Unweighted gap means and counts](ThetaGapBiasThree.lean) · [Pairing the exact class means](ThetaPairBiasThree.lean) · [Euler product for the bias](EXACT-MOD-THREE-BIAS.md)

For any two fixed reduced classes the limiting product law also holds for every continuous joint test of polynomial growth. In particular all mixed moments factor into their individual conditional moments. The ordinary upper sieve controls the numbers of outgoing and incoming edges at each prime. This bounds both pair-coordinate moments by global one-prime moments. After normalization by the number of class pairs, the resulting second-moment bound permits truncation of each joint observable. [Mixed moments and general tests](ThetaClassPairMoments.lean) · [Forward and reverse degree bounds](ThetaPairMarginals.lean) · [Moment bounds](ThetaPairMomentBounds.lean)

For every \(1/15<\theta\le1\), choose a fixed reduced progression and a nonempty open interval of residual values independently for each coordinate. For all large \(X\) and every \(X^\theta\le H\le X\), at least \(\delta XH/(\log X)^2\) pairs meet the two prescriptions, for some fixed \(\delta>0\). In particular either order of opposite residual signs has positive lower frequency at this smaller scale. Both signs concern the centered error. Positivity of \(S(p)\) at all primes remains open. [Two prescribed excursions](ThetaNearbyPrimeExcursions.lean) · [Prime-start and dyadic lower density](ThetaPairExcursionDensity.lean)

## Passing from integer starts to prime starts

An \(o(X)\) integer exception estimate by itself permits every prime start to be exceptional. Fix \(K=\lceil X^{\theta/2}\rceil\). Shifting a window by at most \(K\) changes each normalized sum by at most \(2KB(\log X)^{k+1}/H=o(1)\) if the test has size at most \(B(\log X)^k\) at primes in the band. The absolute Fourier bound gives this condition for every polynomial-growth residual test. A bad prime start forces the next \(K\) integer starts to miss a slightly stricter tolerance, apart from a final strip of at most \(K\) starts. [Shift estimate](ThetaPrimeAnchorTransfer.lean) · [Growth bound](ThetaPrimeAnchorTests.lean)

Select the least remaining bad prime, charge its \(K\) exceptional integers, and discard covered prime starts. Each selected block covers \(O_\theta(K/\log X)\) primes by the translated square sieve. The charged integer blocks are disjoint. This gives \(o(X/\log X)\) bad prime starts, simultaneously for all admitted lengths. The elementary sieve uses the mean of a squared Ramanujan weight with a finite translated remainder. The actual dyadic prime count is asymptotic to \(X/\log X\). The normalized one-window conclusion holds for each continuous test of polynomial growth, including each fixed moment. [Interval sieve](ThetaPrimeIntervalSieve.lean) · [Prime-start charging](ThetaPrimeStartDensity.lean) · [Dyadic denominator](ThetaPairDyadic.lean) · [Prime-count-normalized moments](ThetaPrimeStartMoments.lean)

For a bounded second test the same sieve bounds the normalized inner sum at every prime start. Exceptional starts therefore contribute \(o(1)\) after the first-prime average. The dyadic one-prime theorem gives the first factor. Taking both tests equal to one yields the pair-count normalization. To pass from real product tests to weak convergence, use the complex characteristic functions on the plane and Lévy's convergence theorem. [Product comparison](ThetaPairComparison.lean) · [Normalization](ThetaNearbyPrimePairs.lean) · [Determining tests on the plane](ThetaProductTests.lean)

## Kernel replay

Independent Lean 4.33.1 replay checked 243 modules, including the 225 notebook sources, the pinned DeepMind source, and the external PNT and bridge modules. All 732 distinct axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.

## Ordinary prime inputs

The two numerical thresholds use the ordinary per-length prime estimates of Koukoulopoulos, Theorems 1.1 and 1.2 for the asymptotic and Theorem 1.3 for the lower bound. The Lean statements expose those inputs as \(\texttt{DistributionInput}\) and \(\texttt{LowerInput}\); the passage from these to the pair results is formal. The preceding window note gives the exact fixed-modulus, discrete unweighted comparison. No prime-pair input is used. The supplementary bridge discharges the fixed-progression prime number theorem. [Koukoulopoulos](https://arxiv.org/pdf/1405.6592#page=3) · [Window hypotheses and comparison](ALMOST-ALL-PRIME-WINDOWS.md) · [Checked global PNT bridge](NATURAL-PRIME-MEAN.md)

The DeepMind issue reduces the pointwise conjectures to a remainder. OMA's finite certificate checks the original growth inequality on a bounded range. The previous notebook result on pairs at fixed gaps concerns first-order growth. The present result is a joint limiting distribution of the centered error averaged over a growing range of gaps. [DeepMind](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA](https://github.com/lefttosolve2/open-math-agents/pull/34398) · [LTS](https://lefttosolve.com/p/Arxiv.2501.03234.conjecture_4_2.R1.H1) · [First-order fixed-gap patterns](https://github.com/vincentkoc/solved-conjectures/pull/346)

```lean
import ThetaGapBiasThree
import ThetaNearbyResidualLaw
import ThetaNearbyPrimeExcursions
import ThetaPrimeStartMoments
import ThetaPNTCorollaries

/-! Fixed-modulus prime distribution is supplied by the checked PNT bridge.
The remaining hypotheses concern only ordinary primes in almost all windows. -/
namespace Arxiv.«2501.03234».ThetaNearbyResidualLawPNT
open Real Filter MeasureTheory ThetaProfiniteUnits ThetaPrimeLaw ThetaCharacterPrimeMeans
open ThetaAlmostPrimeDistribution ThetaAlmostPeriodicWindows ThetaNearbyPrimeExcursions
open ThetaPNTCorollaries
open scoped Topology

theorem joint (h : LowerInput) {θ : ℝ} (hθ : 1/15<θ) (ht : θ≤1)
    {q r q' r' : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q)
    (hq' : 0<q') (hr' : r'<q') (hu' : r'.Coprime q') (y z : ℝ) {d e : ℝ} (hd : 0<d) (he : 0<e) :
    ∃ δ : ℝ,0<δ ∧ ∀ᶠ X : ℕ in atTop,∀ H : ℕ,Admits θ X H →
      δ*X*H≤(count X H (selected q r y d) (selected q' r' z e):ℝ)*(log X)^2 :=
  ThetaNearbyPrimeExcursions.joint h progression_mangoldt hθ ht hq hr hu hq' hr' hu' y z hd he

theorem distribution (h : DistributionInput) {θ : ℝ} (hθ : 1/6<θ) (ht : θ≤1) :
    ∃ F : G →₁[haar] ℝ,Represents residual F ∧ ∀ H : ℕ → ℕ,
      (∀ᶠ X : ℕ in atTop,Admits θ X (H X)) →
      Tendsto (fun X => ThetaPairEmpirical.law X (H X)) atTop (𝓝 ((haarLaw F).prod (haarLaw F))) ∧
      Tendsto (fun X : ℕ => (log X/X*(log X/H X))*(ThetaNearbyPrimePairs.count X (H X):ℝ)) atTop (𝓝 1) :=
  ThetaNearbyResidualLaw.distribution h progression_mangoldt hθ ht

theorem classes (h : DistributionInput) {θ : ℝ} (hθ : 1/6<θ) (ht : θ≤1) : ThetaClassPairLaws.ClassPairs θ :=
  ThetaClassPairLaws.original h progression_mangoldt hθ ht

theorem moments (h : DistributionInput) {θ : ℝ} (hθ : 1/6<θ) (ht : θ≤1) : ThetaClassPairMoments.PolynomialPairs θ :=
  ThetaClassPairMoments.original h progression_mangoldt hθ ht

theorem gap_bias (h : DistributionInput) {θ : ℝ} (hθ : 1/6<θ) (ht : θ≤1) : ThetaGapBiasThree.Statement θ :=
  ThetaGapBiasThree.original h progression_mangoldt hθ ht

#print axioms moments
#print axioms gap_bias
#print axioms classes
#print axioms joint
#print axioms distribution
end Arxiv.«2501.03234».ThetaNearbyResidualLawPNT
```
