# Full real support of the residual law of the prime theta sum

Let \(R(p)=S(p)/p-\tfrac12\log p\), with \(S\) the original integer double floor sum. Every nonempty open interval \(I\subset\mathbb R\) occurs with positive lower prime density in **each** reduced progression. For every fixed \(q,r,I\) with \(q>0\), \(0\le r<q\), and \((r,q)=1\), there are \(\delta>0\) and \(X_0\) such that
\[
 \#\{p\le X:p\ \mathrm{prime},\ p\equiv r\bmod q,\ R(p)\in I\}
 \ \ge\ \delta\,\pi(X)\qquad(X\ge X_0).
\]
Consequently the limiting all-prime residual law assigns positive mass to every open ball in \(\mathbb R\). Its support is the entire real line. This fills the gaps left by the earlier result that both tails are unbounded. The theorem includes every fixed class \(1\bmod 2^k\). [Positive prime density and full support](ThetaFullResidualSupport.lean) · [Earlier residual law](PRIME-RESIDUAL-LAW.md) · [Earlier two tails](ALL-CLASS-EXCURSIONS.md) · [Pinned upstream sum](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean#L41-L95)

In fact, given \(0<\kappa<1\), a target interval \(I\), any reduced progression \(r\bmod q\), and any lower cutoff \(N\), there exist \(T\ge N\) and a reduced progression \(a\bmod m_T\) refining \(r\bmod q\), with \(m_T=\operatorname{lcm}(1,\ldots,T)^4\), such that at least a \(1-\kappa\) fraction of its primes up to \(X\) satisfy \(R(p)\in I\) at every sufficiently large \(X\). Here the denominator counts primes in the finer progression itself. The refinement depends on the interval and the tolerated exceptional fraction. The original pointwise positivity and eventual superlinear lower bound remain open. [Refinement theorem](ThetaFullResidualSupport.lean) · [Paper, revised conjectures](https://arxiv.org/pdf/2501.03234v3#page=4)

## Uniform concentration inside each class

Write \(A_T(a)\) for the limiting mean of \(R(p)\) in class \(a\bmod m_T\). For all large \(T\), given any \(\epsilon>0\), every sufficiently large \(X\) simultaneously satisfies, in every reduced class,
\[
 \frac{\sum_{p\le X,\ p\equiv a\bmod m_T}|R(p)-A_T(a)|}
      {\#\{p\le X:p\equiv a\bmod m_T\}}
 \ \le\ C \frac{(\log T)^2}{T^{1/16}}+C T^{-1/4}+\epsilon.
\]
Both sums and counts here run over primes. The endpoint can depend on \(T,\epsilon\). The bound is uniform after dividing by each class's own prime count, even though a class has density \(1/\varphi(m_T)\). [Original class-normalized theorem](ThetaUniformPrimePrediction.lean) · [Fixed progression predictor](ThetaProgressionProjection.lean)

For a finite model of row cutoff \(Y\), expose the complete prime-power factors of \(Y!\) for primes through \(T\). Conditional on the resulting modulus \(M\), every denominator dividing \(m_T\) has the same row value as under conditioning on \(m_T\). For omitted denominators \(d\), set \(g=(M,d)\). Either \(d/g\ge T\), where the reciprocal tail saves \(T^{1/16}\), or \(g\) is divisible by the block \(p^{4\lfloor\log_p T\rfloor}\ge T^2\) of some \(p\le T\). Summing the log-weighted divisor masses of those blocks costs \(O((\log T)^2/T)\). The smaller and larger smooth moduli therefore have conditional means differing by \(O((\log T)^2/T^{1/16})\), uniformly in the full prime-power exponents and residues. [Smooth refinement error](ThetaSmoothRefinement.lean) · [Compact block sizes](ThetaCompactModulus.lean)

The exponential-moment induction for the remaining prime coordinates permits any nonnegative weight already fixed by the exposed coordinates. Choose the indicator of the specific compact class. The complete exponential moment is bounded by a constant times the *mass of that class*. Dividing by its mass gives \(O(T^{-1/4})\) absolute mean fluctuation about the fully exposed prediction. Ordinary PNT in fixed progressions transfers the periodic finite estimates to primes. The prior mean-absolute approximation to \(R\) permits the cutoff to depend on the compact class. [Weighted moment induction](ThetaCenteredExposure.lean) · [Finite conditional concentration](ThetaClassConcentration.lean) · [Conditional prime transfer](ThetaConditionalApproximation.lean)

## Interpolation in a prescribed progression

The difference between child and parent predictors tends uniformly to zero:
\[
 \sup_{(a,m_{T+1})=1}|A_{T+1}(a)-A_T(a\bmod m_T)|\longrightarrow0.
\]
For finite models, compare the two compact predictors to complete smooth projections along the same lifted unit. Revealing one more coordinate changes the projection by \(O((\log(T+1))^2/(T+1))\). The two compact-approximation errors also tend to zero. Taking both finite models sufficiently accurate in the same two fixed prime classes yields the assertion for the original predictors. [Predictor increment](ThetaPredictionSteps.lean)

Deep inside \(r\bmod q\), choose a class with mean below the target, then a further refinement with mean above it, using the prior signed extreme finite means. Along the nested compact moduli on that refinement, the first crossing has overshoot tending uniformly to zero. Thus an arbitrarily fine class has predictor as close to the target as prescribed. The class-normalized error bound and Markov's inequality put a fraction \(1-\kappa\) inside the target interval. The class has positive prime density, and the closed-ball inequality for the limiting law gives positive mass to every open ball. [Dense conditional predictors](ThetaDensePredictors.lean) · [Extreme finite means](ThetaReflectedWindowMeans.lean) · [Weak-convergence transfer](ThetaPrimeResidualLaw.lean)

## Kernel replay

Independent Lean 4.33.1 replay checked 122 modules, including the 104 notebook sources, the pinned DeepMind source, and the external PNT and bridge modules. All 507 distinct axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.

## Source comparison and external theorem

Berndt, Bhat, Meyer, Xie and Zaharescu study the signed aggregate and pointwise lower growth. Lägeler studies individual Hardy sums under a different sampling rule. The DeepMind issue reduces the pointwise conjectures to remainder estimates. The OMA and LTS records checked by paper ID concern harmonic reductions and finite bounds, including \(2p<S(p)\) for primes \(233<p<100000\). A prime-density theorem for \(R(p)\) in every bounded open interval is a distinct statement. The proof gives no density formula for a specified interval, absolute continuity, atomlessness or effective lower bound for \(\delta\). [Original paper](https://doi.org/10.1007/s00025-025-02584-2) · [Lägeler](https://arxiv.org/abs/2207.04828) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA finite partial](https://github.com/lefttosolve2/open-math-agents/pull/31296) · [OMA finite lower bound](https://github.com/lefttosolve2/open-math-agents/pull/34398) · [Corresponding LTS target](https://lefttosolve.com/p/Arxiv.2501.03234.conjecture_4_2.R1.H1)

The notebook module states its ordinary fixed-progression PNT premise explicitly. The following companion uses the previous pinned formal proof of that input. It exports the density and law for the original sum with no analytic assumptions. Use the joint replay instructions with this block named `ThetaFullResidualSupportPNT.lean`. [PNT bridge and pinned checkout](NATURAL-PRIME-MEAN.md#joint-lean-replay) · [Formal PNT source](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/55270df807213fc3584523d09e0311d7dc073ff5/PrimeNumberTheoremAnd/Wiener.lean)

```lean
import ThetaFullResidualSupport
import ThetaPNTCorollaries

/-! Prime-density and full-support conclusions with the fixed-progression PNT discharged. -/

namespace Arxiv.«2501.03234».ThetaFullResidualSupportPNT
open Finset Filter MeasureTheory ThetaClassConcentration ThetaProfiniteUnits ThetaPrimeLaw
open ThetaPNTCorollaries ThetaCharacterPrimeMeans ThetaFullResidualSupport
open scoped Topology

theorem original {q r : ℕ} (hq : 0<q) (hr : r<q) (hc : r.Coprime q) (y : ℝ) {d : ℝ} (hd : 0<d) :
    ∃ δ : ℝ, 0<δ ∧ ∀ᶠ X : ℕ in atTop,
      δ*X.primeCounting≤((ThetaPrimeDensity.primeSet (fun p => p%q=r ∧ |(S p:ℝ)/p-Real.log p/2-y|<d) X).card:ℝ) :=
  density progression_mangoldt hq hr hc y hd

theorem arbitrarily_concentrated {q r : ℕ} (hq : 0<q) (hr : r<q) (hc : r.Coprime q)
    (y : ℝ) {d κ : ℝ} (hd : 0<d) (hκ : 0<κ) (N : ℕ) :
    ∃ T≥N, q∣m T ∧ ∃ a< m T, a.Coprime (m T) ∧ a%q=r ∧ ∀ᶠ X : ℕ in atTop,
      (1-κ)*((ThetaPrimeDensity.primeSet (fun p => p%m T=a) X).card:ℝ)≤((hits (m T) a y d X).card:ℝ) :=
  refinement progression_mangoldt hq hr hc y hd hκ N

theorem law : ∃ F : G →₁[haar] ℝ, Represents residual F ∧
    Tendsto (empirical residual) atTop (𝓝 (haarLaw F)) ∧
    ∀ y : ℝ, ∀ d>0, 0<(haarLaw F : Measure ℝ) (Metric.ball y d) := by
  obtain ⟨F,hF,_⟩ := S_prime_residual_distribution progression_mangoldt
  exact ⟨F,hF,empirical_tendsto progression_mangoldt hF,fun y _ hd => full_support progression_mangoldt hF y hd⟩

#print axioms original
#print axioms arbitrarily_concentrated
#print axioms law
end Arxiv.«2501.03234».ThetaFullResidualSupportPNT
```
