# The theta residual law in short prime intervals

Let \(R(p)=S(p)/p-\tfrac12\log p\) for the signed sum in the pinned DeepMind source. Fix \(7/12<\theta\le1\), a reduced progression \(r\bmod q\), and an open residual interval \((y-d,y+d)\) with \(d>0\). There is \(\delta>0\) such that at every sufficiently large integer \(X\), simultaneously for every integer \(X^\theta\le H\le X\),
\[
 \#\{X<p\le X+H:\ p\ \mathrm{prime},\ p\equiv r\bmod q,\ |R(p)-y|<d\}
 \ \ge\ \delta\,H/\log X .
\]
Here \(\delta\) can depend on the fixed progression, interval and exponent. Moreover, given \(\kappa>0\), one can fix a single reduced subprogression of arbitrarily large compact-modulus depth such that at least \(1-\kappa\) of **its own primes** lie in the prescribed residual interval throughout all these windows. [Short-window counts and refinement](ThetaShortResidualSupport.lean) · [Global full-support theorem](FULL-RESIDUAL-SUPPORT.md) · [Pinned signed sum](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean)

For each fixed reduced progression \(r\bmod q\), the **whole empirical residual law within that class** converges, including every continuous test of polynomial growth. The normalization is the actual number of primes in that class in the short window. All classes and all admissible length sequences \(H(X)\) use the same profinite representative \(F\). If \(U\) has Haar distribution on the profinite units, the limit is
\[
  \mathcal L\bigl(F(U)\mid U\equiv r\pmod q\bigr).
\]
This conditional law has support \(\mathbb R\) for every reduced residue. For odd \(m\), the law in a reduced class \(b\bmod 2^j m\) equals the law in \(b\bmod m\). In particular, every class \(1\bmod 2^j\), including \(1\bmod8\), has the **all-prime** limiting distribution and all its signed and absolute moments. The same weak limits, polynomial-growth tests, and equality on dyadic refinements also hold for ordinary primes up to \(X\), using only fixed-progression PNT. [Conditional law and dyadic refinements](ThetaClassResidualLaws.lean) · [Polynomial-growth tests in short windows](ThetaShortConditionalTests.lean) · [Global dyadic restriction](ThetaDyadicLaw.lean)

For every admissible length sequence \(H(X)\), the empirical probability measures of \(R(p)\) on the primes in \((X,X+H(X)]\) converge weakly to the same Haar pushforward as the primes up to \(X\). Every fixed signed moment converges to the corresponding moment of this law. The empirical mean divides by the actual number of primes in the short interval. More generally, for any fixed bounded periodic shift \(w\), periodic multiplier \(|g|\le1\), and integer \(k\ge0\), the averages of \(g(p)(w(p)+R(p))^k\) in the short interval and in \((X,2X]\), each divided by its logarithmic-integral mass, differ by \(o(1)\) uniformly in \(H\). The same comparison holds for \(g(p)\varphi(R(p))\) and every Lipschitz test \(\varphi\). [Weak and moment limits](ThetaShortResidualLaw.lean) · [Mixed moments](ThetaLocalMomentComparison.lean) · [Weighted tests](ThetaLocalLipschitzTransfer.lean)

## Proof

Use one power band \(N^{56}\le X<X+H\le N^{64}\) that also covers \((X,2X]\). At kernel exponent \(e\), multiply the earlier denominator cutoff by one additional dyadic level, taking \(J=N^e\ell^4\), where \(\ell=1+\lfloor\log_2 N\rfloor\). After division by \(p\) the deterministic off-diagonal error is at most \(4600600/\ell\) once \(\ell^2\le N\). The change of the low-row weights costs at most \(3Y/N\). The discarded denominator rows have translated square energy
\[
 \ll (1+\log N)^9\bigl(H/Y^{1/64}+N^e\bigr).
\]
For the \(k\)-th absolute error moment choose \(Y=\lfloor\log X\rfloor^{64(2k+13)}\). The strict inequality \(e/64<\theta\) absorbs every fixed logarithmic factor multiplying \(N^e\). On the exceptional primes use the pointwise \(O((\log X)^2)\) bound for the residual and its model. This proves approximation in every fixed power mean by the same finite model for all lengths at a given endpoint. [Cone estimate](ThetaLocalVanishingCone.lean) · [Translated energy](ThetaLocalResidualEnergy.lean) · [Prime approximation](ThetaLocalMomentApproximation.lean)

Expanding a \(k\)-th power uses tuples of \(k\) rows. With fixed modulus \(q\) for both the shift and the multiplier, each summand has period at most \(qY^k\). Ordinary short-interval equidistribution therefore transfers each normalized moment against a single complete mean. The common period of the whole model can be much bigger. Comparison with the long window gives bounded higher moments. The resulting power-error estimate passes the signed moments to the original residual. A single fixed periodic predictor also has arbitrarily small mean-square error on every eligible interval. This passes Lipschitz tests to the Haar law. To obtain the count, use a continuous tent supported in the prescribed interval and the known global subprogression concentration. [Row products](ThetaLocalPowerDiscrepancy.lean) · [Prime transfer](ThetaLocalSampledPowers.lean) · [Fixed predictor](ThetaLocalPeriodicPrediction.lean) · [Counting test](ThetaLocalIntervalTests.lean)

## Conditioning on a residue class

At the factorial level \(q!\), the indicator of \(r\bmod q\) is a continuous profinite cylinder of Haar mass \(1/\varphi(q)\). Multiplying a representative by its indicator corresponds to setting the prime sequence to zero outside the class. Composing with a Lipschitz test preserves its simultaneous approximation on primes and in Haar mean. This identifies the limiting weighted integral. Dividing by the class's own prime count gives the conditional probability law. The earlier dyadic restriction for odd-period tests and the Chinese remainder theorem identify the limits after adjoining a power of two. [Conditioning the representative](ThetaConditionalHaar.lean) · [Class normalization](ThetaShortClassMeans.lean) · [Weak convergence](ThetaShortConditionalLaw.lean)

For a test bounded by \(K(1+|x|^k)\), truncating its values at height \(M\) costs at most \(2K^2(1+\operatorname{mean}(R^{2k}))/M\). The short-window moment bound persists in any fixed class because its count is comparable to the total count in that window. Truncation gives convergence of the actual class means for continuous tests, including unbounded ones. [Finite truncation](ThetaWindowTruncation.lean) · [Class moment bound](ThetaShortConditionalTests.lean)

## Kernel replay

Independent Lean 4.33.1 replay checked 200 modules, including the 181 notebook sources, the pinned DeepMind source, and the external PNT and bridge modules. All 664 distinct axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.

## Inputs and scope

The Lean theorem takes the ordinary short-interval progression estimate explicitly. For all fixed \(A,B\), it requires discrepancy at most \(H/(\log X)^B\) from \(\varphi(q)^{-1}\int_X^{X+H}dt/\log t\), uniformly over reduced residues for \(q\le(\log X)^A\). With the elementary complete-sum bound the proof works for \(3/4<\theta\le1\). With the classical Weil bound it works for \(1/2<\theta\le1\) under the same progression hypothesis. The cited prime-count theorem supplies that hypothesis for \(\theta>7/12\); the conversion from log-weighted to ordinary counts is recorded in the short-excursion note. The fixed-progression global PNT is supplied by the separate Lean bridge below. [Lean statement and two exponents](ThetaShortPrimeDistribution.lean) · [Prime-count input](ThetaLocalPrimeCounts.lean) · [Partial summation](SHORT-PRIME-EXCURSIONS.md) · [Thorner and Zaman, Theorem 1.1 and Remark 1.2](https://arxiv.org/pdf/2108.10878#page=3) · [Weil](https://doi.org/10.1073/pnas.34.5.204)

These are statements about the residual of the original aggregate on ordinary primes. The pointwise positivity conjecture remains open here. The active DeepMind issue records a common carry-count reduction. The OMA finite certificate addresses a pointwise range. Neither establishes a limiting short-interval distribution for this aggregate. [Berndt et al., v3](https://arxiv.org/pdf/2501.03234v3#page=4) · [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA finite bound](https://github.com/lefttosolve2/open-math-agents/pull/34398) · [LTS finite target](https://lefttosolve.com/p/Arxiv.2501.03234.conjecture_4_2.R1.H1)

A separate project gives a Lean identity in terms of single Hardy sums, an independent written upper bound for the aggregate, and numerical checks through two million. [Independent partial result](https://github.com/umaia1234/agentic-conjectures/pull/65)

The bridge imports the same compatible WeakPNT_AP proof as the [ordinary prime means](NATURAL-PRIME-MEAN.md).

```lean
import ThetaShortPrimeDistribution
import ThetaPNTCorollaries

/-! The fixed-progression global prime theorem is supplied by WeakPNT_AP. -/
namespace Arxiv.«2501.03234».ThetaShortPrimeDistributionPNT
open ThetaLocalPrimeCounts ThetaShortPrimeDistribution ThetaPNTCorollaries

theorem elementary {θ : ℝ} (hθ : 3/4<θ) (h₁ : θ≤1) (h : Ordinary θ) : Statement θ :=
  ThetaShortPrimeDistribution.elementary hθ h₁ h progression_mangoldt

theorem weil {θ : ℝ} (hθ : 1/2<θ) (h₁ : θ≤1) (hw : ThetaWeilShortIntervals.Weil)
    (h : Ordinary θ) : Statement θ :=
  ThetaShortPrimeDistribution.weil hθ h₁ hw h progression_mangoldt

#print axioms elementary
#print axioms weil
end Arxiv.«2501.03234».ThetaShortPrimeDistributionPNT
```

The class-normalized companion is `ThetaShortConditionalPNT.lean`. Its `ordinary` and `odd_part` declarations discharge fixed-progression PNT. Its two short-window declarations state the ordinary short-interval and complete-sum inputs at their respective exponents.

```lean
import ThetaClassResidualLaws
import ThetaPNTCorollaries

/-! Fixed-progression conditional Haar laws from the pinned ordinary PNT. -/
namespace Arxiv.«2501.03234».ThetaShortConditionalPNT
open MeasureTheory Filter ThetaProfiniteUnits ThetaPrimeLaw ThetaDyadicLaw ThetaCharacterPrimeMeans
open ThetaConditionalHaar ThetaShortConditionalLaw ThetaClassResidualLaws ThetaPNTCorollaries
open ThetaLocalPrimeCounts ThetaCalibratedCone
open scoped Topology

theorem ordinary : ∃ F : G →₁[haar] ℝ,Represents residual F ∧ ∀ q r : ℕ,
    0<q → r<q → r.Coprime q → ∃ hc : haar (fibre q r)≠0,
      Tendsto (progressionLaw q r residual) atTop (𝓝 (law F hc)) ∧
      ∀ y : ℝ,∀ d>0,0<(law F hc : Measure ℝ) (Metric.ball y d) := by
  obtain ⟨F,hF⟩ := exists_haar_representative progression_mangoldt residual_approximable
  exact ⟨F,hF,fun _ _ hq hr hu =>
    ⟨positive progression_mangoldt hq hr hu,ThetaClassResidualLaws.ordinary progression_mangoldt hq hr hu hF,
      fun y _ hd => full_support progression_mangoldt hq hr hu hF y hd⟩⟩

theorem prefix_tests {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q)
    {F : G →₁[haar] ℝ} (hF : Represents residual F) {φ : ℝ → ℝ} (hp : Continuous φ)
    {K : ℝ} (k : ℕ) (hg : ∀ x,|φ x|≤K*(1+|x|^k)) :
    Tendsto (progressionMean q r (fun p => φ ((S p:ℝ)/p-Real.log p/2))) atTop
      (𝓝 (∫ x,φ x ∂(law F (positive progression_mangoldt hq hr hu)))) :=
  ordinary_tests progression_mangoldt hq hr hu hF hp k hg

theorem elementary {θ : ℝ} (hθ : 3/4<θ) (h₁ : θ≤1) (h : Ordinary θ) : Windows θ :=
  windows (e:=48) (by decide) (le_refl 48) elementary_kernel (by norm_num;linarith) h₁ h progression_mangoldt

theorem weil {θ : ℝ} (hθ : 1/2<θ) (h₁ : θ≤1) (hw : ThetaWeilShortIntervals.Weil)
    (h : Ordinary θ) : Windows θ :=
  windows (e:=32) (le_refl 32) (by decide) (ThetaWeilShortIntervals.kernel hw)
    (by norm_num;linarith) h₁ h progression_mangoldt

theorem odd_part {q k b : ℕ} (hq : Odd q) (hb : b<2^k*q) (hu : b.Coprime (2^k*q))
    {F : G →₁[haar] ℝ} (hF : Represents residual F) :
    ∃ hc : haar (fibre q (b%q))≠0,
      law F (positive progression_mangoldt (by omega : 0<2^k*q) hb hu)=law F hc :=
  ThetaClassResidualLaws.odd_part progression_mangoldt hq hb hu hF

#print axioms prefix_tests
#print axioms ordinary
#print axioms elementary
#print axioms weil
#print axioms odd_part
end Arxiv.«2501.03234».ThetaShortConditionalPNT
```
