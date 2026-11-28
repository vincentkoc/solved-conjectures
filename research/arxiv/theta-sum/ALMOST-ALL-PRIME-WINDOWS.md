# Theta growth and sign changes in almost all short prime intervals

Write \(S(p)\) for the original signed integer sum and \(R(p)=S(p)/p-\tfrac12\log p\). The starting points below are **integers** \(X\le n<2X\). A window contains the primes \(n<p\le n+H\). [Pinned DeepMind sum and conjectures](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean#L41-L97) · [Berndt et al., revised conjectures](https://arxiv.org/pdf/2501.03234v3#page=4)

**The original lower conjecture.** There is an absolute \(a>0\) such that, for every natural number \(k\) and every sufficiently large \(X\), put \(V=\exp(a(\log X)^{3/4})\). Outside at most \(12X/V\) starting points, **simultaneously for every integer \(1\le H\le X\)**,
\[
 \#\{n<p\le n+H:\ p\text{ odd prime},\ S(p)\le kp\}\le \frac{H}{V\log X}.
\]
This is unconditional in Lean. The relative-error theorem has the same form for \(|S(p)-p\log p/2|\ge\varepsilon p\log p\), with \(a\) depending on \(\varepsilon>0\). The exponent coefficient for the integer-slope statement is independent of \(k\). In particular every prime in a window of length \(H<V\log X\) from a good start satisfies the indicated lower slope once \(X\) is sufficiently large for that slope. The estimate counts exceptions and leaves pointwise positivity open. [Theorems original and pinned](ThetaAlmostFirstOrder.lean) · [Global input](ThetaCenteredOriginalTail.lean)

**Adjacent crossings.** For \(1/15<\theta<1\), every fixed reduced class \(r\bmod q\) has at least \(X^{1-\theta}/4\) distinct pairs of consecutive progression primes in \((X,2X]\) with \(R(p)R(p')<0\), for all sufficiently large integer \(X\). Taking \(q=1\) gives consecutive ordinary primes. For \(1/15<\theta\le1\) and each fixed \(y\in\mathbb R,d>0\), some \(\delta>0\) gives
\[
 \#\{n<p\le n+H:\ p\equiv r\bmod q,\ |R(p)-y|<d\}\ \ge\ \delta H/\log X
\]
for every \(X^\theta\le H\le X\), outside \(o(X)\) starts. The exceptional set may depend on the class and test interval. The source of the ordinary prime-count input is Koukoulopoulos's Theorem 1.3. [Original-residual statements](ThetaAlmostPrimeDistribution.lean) · [Crossing count](ThetaAlmostCrossings.lean) · [Koukoulopoulos, p. 3](https://arxiv.org/pdf/1405.6592#page=3)

**Limiting law.** For \(1/6<\theta\le1\), the empirical law of \(R(p)\) on the primes of a window converges weakly to the previously constructed Haar pushforward. The normalization divides by the actual number of primes in that window. Every continuous real test of at most polynomial growth converges to its integral, including every fixed signed moment. For any specified weak neighborhood, or a test and error tolerance, the proportion of starts where *some* admissible length violates it tends to zero. The Lean filter on triples \((X,n,H)\) encodes precisely this quantifier and is nontrivial for \(\theta\le1\). Koukoulopoulos's Theorem 1.2 provides the ordinary input here. [Limit theorem](ThetaAlmostWindowLaw.lean) · [Polynomial-growth approximation](ThetaPrimeTestApproximation.lean) · [Koukoulopoulos, pp. 2–3](https://arxiv.org/pdf/1405.6592#page=3)

**Conditional law in each progression.** For the same \(1/6<\theta\le1\), restrict the primes in the window to any fixed reduced class \(r\bmod q\) and divide by their own count. The empirical measures converge weakly to the law of \(F(U)\) for a Haar unit conditioned on \(U\equiv r\bmod q\). The same limit holds for every continuous polynomial-growth test. For each fixed test and tolerance, one exceptional set of \(o(X)\) starting points suffices for all admissible lengths. Since the class law depends only on the odd part of the modulus under compatible refinement, the class \(1\bmod 8\) has the all-prime limit. [Class-normalized theorem](ThetaAlmostClassLaws.lean) · [Haar law and dyadic invariance](SHORT-RESIDUAL-LAW.md)

## Transfer to all lengths

For an exceptional starting point select a witness \(H>0\) where the average of a nonnegative sequence exceeds \(t\). Choose the leftmost start \(n\), charge the mass in \((n,n+H]\), and remove the starting integers in \([n,n+H)\). The charged windows are disjoint. Their mass bounds \(t\) times the number of exceptional starts. This constant-one inequality allows arbitrary lengths even when chosen after inspecting the data. Applying it to the global prime approximation error, with \(\pi(3X)\log X\le12X\), transfers an \(L^1\) periodic approximation to almost all starts. For the unconditional assertion apply it to the indicator of the first-order exceptional primes. [Finite maximal inequality](ThetaMaximalWindow.lean) · [Prime-normalized error budget](ThetaWindowApproximation.lean)

A fixed periodic nonnegative test needs only lower counts in its reduced residue classes. For the excursion result, use a nonnegative tent test supported on the desired residual interval, multiplied by the progression indicator. Global positive lower density in its half-radius interval supplies a positive mean. A nonnegative periodic approximation retains at least half that mean. At the stronger counting threshold, two-sided estimates give the limit of every periodic test. Clipping the residual on a compact interval and controlling the discarded part by one higher global moment handles polynomial growth. [Lower and two-sided transfers](ThetaAlmostTransfer.lean) · [Tent-test counts](ThetaAlmostExcursions.lean) · [Global full support](FULL-RESIDUAL-SUPPORT.md)

For the class law, multiply the test by its progression indicator before periodic approximation. The scaled numerator converges to the class integral divided by the totient. The scaled count converges to the reciprocal totient on the same window filter. Dividing cancels both scalings and eventually divides by a positive count. [Numerator and denominator transfer](ThetaAlmostClassLaws.lean)

Each window with both signs beyond the possible single zero of \(R(p)\) contains a strictly crossing adjacent pair. A crossing can witness at most \(H\) integer starts at the chosen length \(H=\lceil X^\theta\rceil\). Restricting the starts to windows ending by \(2X\) gives the factor \(1/4\). This improves the dyadic crossing exponent for **fixed** residue classes. The earlier theorem controls **every** long window and allows the modulus and excursion height to grow. [Every-window comparison](SHORT-PRIME-EXCURSIONS.md) · [Adjacency lemma](ThetaConsecutiveCrossings.lean)

## Kernel replay

Independent Lean 4.33.1 replay checked 227 modules, including the 209 notebook sources, the pinned DeepMind source, and the external PNT and bridge modules. All 709 distinct axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.

## Ordinary input and replay scope

The Lean hypotheses are per-length estimates for **ordinary unweighted prime counts** at fixed moduli. They ask for at most \(X/(\log X)^2\) bad starts for each \(H\); the bad set can change with \(H\). A grid of at most \((1+\lfloor\log_2 X\rfloor)(2K+1)\) lengths brackets \(H\) to relative error \(1/K\). A union bound and monotonicity of the unnormalized counts produce the shared exceptional set. A strict gap between exponents \(\beta<\theta\) allows the lower bracket to remain admissible. [Grid and cardinality](ThetaWindowGrid.lean) · [Ordinary hypotheses and interpolation](ThetaAlmostPrimeCounts.lean)

For the lower input, fix \(1/15<\beta<1\) and choose the paper's \(\varepsilon\) strictly between zero and \(\beta-1/15\). Apply Theorem 1.3 with \(x=2X,\ Q=q,\ h=H\). For fixed \(q\) the size condition eventually holds uniformly for \(X^\beta\le H\le X\). The exceptional-pair bound is \(O_{\varepsilon,A}(qX/(\log X)^A)\); it bounds the exceptions for this particular modulus. Since \(p\le3X\), dividing the weighted count by \(\log(3X)\le2\log X\) gives a lower constant independent of the fixed modulus. Take \(A>2\) to meet the Lean bound. [Theorem 1.3](https://arxiv.org/pdf/1405.6592#page=3)

For \(1/6<\beta<1\), Theorem 1.2 with \(x=X,\ Q=q\) gives a log-power saving in the integral of the maximum weighted class discrepancy throughout \(X\le y\le2X\). The modulus constraint holds uniformly for \(X^\beta\le H\le X\) once the paper's \(\varepsilon\) is sufficiently small. For integer \(H\) and \(n\), the weighted count at real starts is constant on \([n,n+1)\). Markov's inequality bounds the number of bad integer starts at each length. The factor \(\log p/\log X=1+O(1/\log X)\) is uniform throughout the window. Nonunit classes contain no primes once \(X>q\). Taking a larger log-power saving yields the specified per-length exception count for each fixed positive discrepancy tolerance. These two published analytic inputs are external to the Lean proof. [Theorems 1.1 and 1.2](https://arxiv.org/pdf/1405.6592#page=2)

The notebook has checked the original global law and pointwise reductions separately. The public DeepMind issue addresses a pointwise remainder bound. OMA's finite certificate covers \(233<p<100000\). Searches by arXiv identifier, adjacent residual crossings, and short-window distribution did not identify a matching formal result as of 2026-11-28. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA finite certificate](https://github.com/lefttosolve2/open-math-agents/pull/34398) · [LTS target](https://lefttosolve.com/p/Arxiv.2501.03234.conjecture_4_2.R1.H1)

The supplementary bridge below uses the existing fixed-progression prime number theorem. The ordinary short-window assumptions are explicit. [Global PNT bridge and pin](NATURAL-PRIME-MEAN.md)

```lean
import ThetaAlmostPrimeDistribution
import ThetaAlmostClassLaws
import ThetaPNTCorollaries

/-! The documented fixed-progression PNT supplies the global prime input. -/
namespace Arxiv.«2501.03234».ThetaAlmostPrimeDistributionPNT
open Real Finset Filter ThetaAlmostPrimeDistribution ThetaAlmostPeriodicWindows
open ThetaWindowApproximation ThetaLocalPrimeCounts ThetaPNTCorollaries

theorem crossings (h : LowerInput) {θ : ℝ} (hθ : 1/15<θ) (ht : θ<1)
    {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q) :
    ∀ᶠ X : ℕ in atTop, (X:ℝ)^(1-θ)/4≤((ThetaCrossingFrequency.starts X q r).card:ℝ) :=
  ThetaAlmostPrimeDistribution.crossings h progression_mangoldt hθ ht hq hr hu

theorem excursions (h : LowerInput) {θ : ℝ} (hθ : 1/15<θ) (ht : θ≤1)
    {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q) (y : ℝ) {d : ℝ} (hd : 0<d) :
    ∃ δ : ℝ, 0<δ ∧ Almost (fun X n => ∀ H : ℕ, Admits θ X H →
      δ*H/log X≤(((sample n H).filter (fun p => p%q=r ∧ |(S p:ℝ)/p-log p/2-y|<d)).card:ℝ)) :=
  ThetaAlmostPrimeDistribution.excursions h progression_mangoldt hθ ht hq hr hu y hd

theorem distribution (h : DistributionInput) {θ : ℝ} (hθ : 1/6<θ) (ht : θ≤1) : Law θ :=
  ThetaAlmostPrimeDistribution.distribution h progression_mangoldt hθ ht

theorem classes (h : DistributionInput) {θ : ℝ} (hθ : 1/6<θ) (ht : θ≤1) : ThetaAlmostClassLaws.ClassLaw θ :=
  ThetaAlmostClassLaws.original h progression_mangoldt hθ ht

#print axioms classes
#print axioms crossings
#print axioms excursions
#print axioms distribution
end Arxiv.«2501.03234».ThetaAlmostPrimeDistributionPNT
```
