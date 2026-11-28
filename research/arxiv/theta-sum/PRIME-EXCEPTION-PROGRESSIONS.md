# Theta sign exceptions summed over the worst residue classes

Write \(w(X)=1+\log\log X\), \(s(X)=\log X/(2^{28}w(X))\). For any fixed natural \(k\), all sufficiently large \(X\), and every \(Q\) with \(Q^2\le X e^{s(X)}\),
\[
\sum_{q\le Q}\max_{0\le b<q}
\#\{p\le X : p\text{ prime},\ p\equiv b\pmod q,\ S(p)\le kp\}
\ \le\ \pi(X)e^{-2s(X)}.
\]
The sum starts at \(q=1\). Each modulus can choose its own worst residue, including a nonreduced residue. The same estimate applies to the primes with \(\lvert S(p)/p-\tfrac12\log p\rvert\ge A(1+\log\log p)^2\) for an absolute \(A>0\). These are unconditional Lean statements for the original signed integer sum. Taking \(k=0\) bounds all failures of strict positivity. The argument does not establish positivity at every odd prime. [Original exception counts](ThetaWorstPrimeClasses.lean) · [Pinned DeepMind declarations](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean) · [Original paper](https://arxiv.org/pdf/2501.03234v3#page=4)

## Consequence for distribution in progressions

Choose cutoffs \(y_q\le X\), residues \(b_q<q\), and any real main terms \(M_q\). Imposing \(S(p)>kp\) on the usual prime count changes the sum of the absolute progression errors against \(M_q\) by at most \(\pi(X)e^{-2s(X)}\), simultaneously for all these choices. For each fixed \(A>0\), this error is \(O(X/(\log X)^A)\). In particular, the Bombieri–Vinogradov estimate for ordinary primes transfers to the primes satisfying the original slope at its usual levels. Lean proves the equivalence of the two distribution estimates for every level function with \(Q(X)^2\le Xe^{s(X)}\) eventually. Ordinary prime equidistribution beyond the square-root range is a separate question. [Finite comparison](ThetaPositiveDistribution.lean) · [Exact transfer at every logarithmic error exponent](ThetaPositivePrimeLevel.lean) · [Classical theorem and its level, Pascadi, introduction](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/S0010437X2500747X)

For all but at most \(Qe^{-s(X)}\) moduli up to \(Q\), every class containing at least \(\pi(X)/Q\) ordinary primes loses a fraction strictly smaller than \(e^{-s(X)}\) when the slope condition is imposed. The same excluded set works for every residue of a given modulus. [Prime-rich classes](ThetaPrimeRichClasses.lean)

The pure definition prefix in the pinned Bombieri–Vinogradov challenge uses `Set.ncard`, inclusive real endpoints, unit residues and \(\pi(\lfloor x\rfloor)/\varphi(q)\). Lean checks by reflexivity that the ordinary premise of the direct adapter is the external proposition. The transfer holds for every real endpoint \(x\ge3\) with all of the source's quantifiers, including negative \(\theta\). It preserves the main term and the inclusive modulus cutoff when counting primes with \(S(p)>kp\). Assuming that proposition, for every \(\theta<1/2,A>0\) and \(Q=\lfloor X^\theta\rfloor\), all but \(O_{A,k,\theta}(Q/(\log X)^A)\) moduli up to \(Q\) have at least \(\pi(X)/(2\varphi(q))\) primes satisfying the slope in **every** reduced class. This last arithmetic-progression conclusion uses ordinary prime distribution. The unconditional estimates above already bound the total cost of discarding the bad primes. [All real endpoints](ThetaRealPrimeClassBV.lean) · [Unit classes](ThetaPrimeClassBV.lean) · [Coverage of all reduced classes](ThetaPrimeClassCoverage.lean) · [Pinned ordinary proposition](https://github.com/kimihiro64/bombieri-vinogradov/blob/7a1748306e026825ed6a5555516cc2f28989b2ac/Challenge.lean) · [Ordinary proof entry point](https://github.com/kimihiro64/bombieri-vinogradov/blob/7a1748306e026825ed6a5555516cc2f28989b2ac/Solution.lean)

## Least prime with a prescribed theta slope

Fix a natural \(k\). Assuming the ordinary Bombieri–Vinogradov proposition above, for every \(t>2\), \(u<t\) and \(A>0\) all but \(O_{A,k,t,u}(Q/(\log Q)^A)\) of the moduli \(q\le Q\) have the following property. **Every** reduced class modulo \(q\) contains a prime \(q^u<p\le q^t\) with \(S(p)>kp\). The same polynomial window contains a prime with \(\lvert S(p)/p-\tfrac12\log p\rvert < B(1+\log\log p)^2\), for an absolute \(B>0\). Both endpoints use the individual modulus \(q\). To obtain them, put \(d=(\max(2,u)+t)/2\), \(\gamma=(d+t)/(2t)<1\) and \(X=\lceil Q^d\rceil\). The coverage estimate at level \(1/d<1/2\) covers every \(q\le Q\); its modulus cutoff is at most \(2Q\). Discard the \(q\le Q^\gamma\), which cost \(O(Q/(\log Q)^A)\). At the surviving moduli one has \(X\le q^t\). A residue class contains at most \(1+Z/q\) integers up to \(Z\). Its selected count therefore forces a prime above \(\pi(X)/8\), which exceeds \(q^u\) for large \(Q\). [Polynomial windows for typical moduli](ThetaTypicalLeastPrime.lean) · [Lower endpoint](ThetaLateClassWitness.lean)

A separate argument covers **every sufficiently large modulus**. Maynard's Theorem 3.2 gives an ordinary class count \(\gg X\log q/(\sqrt q\,\varphi(q)\log X)\) for every reduced class, \(q\) sufficiently large and \(X\ge q^8\). If \(q\le e^{s(X)}\), that count is at least \(Xe^{-4s(X)}\) for sufficiently large \(X\). The unconditional global theta exception count is at most \(Xe^{-8s(X)}\). Thus at most an \(e^{-4s(X)}\) fraction of the primes in **each** of those classes fails the slope. The same relative bound holds for the centered exceptions at height \(A(1+\log\log p)^2\) for an absolute \(A>0\). Taking \(X=\lceil\exp(2^{31}\log q(1+\log\log q))\rceil\) gives at least one prime in every reduced class with
\[
 S(p)>kp,\qquad p\le q^{2^{32}(1+\log\log q)} .
\]
The same upper bound holds for a prime satisfying the centered inequality with an absolute residual constant. The Lean premise in this argument is precisely the ordinary lower bound, restricted to integer endpoints and multiplied by its positive denominator. It is independent of the ordinary Bombieri–Vinogradov premise. [All-class relative counts](ThetaUniformPrimeClasses.lean) · [Least prime in each reduced class](ThetaLeastSlopePrime.lean) · [Maynard, Theorem 3.2](https://ora.ox.ac.uk/objects/uuid%3Af34a2af4-c36d-4f9b-bad7-016a7a989203/files/m22685a8edf2e5142a452f7a8fd0f6ea3#page=4)

## Kernel replay

Independent Lean 4.33.1 replay checked 135 modules, including the 132 notebook sources and the pinned DeepMind source and two direct external comparison modules. All 545 distinct axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.

## The elementary counting argument

For any finite set \(E\) in an interval \([u,u+H]\), choose one residue \(a(q)\) for each \(q\le Q\). Write \(F(n)=\sum_{q\le Q}\mathbf{1}_{n\equiv a(q)\bmod q}\). Any two integers satisfying both of a pair of residue conditions are congruent modulo \(\operatorname{lcm}(q,d)\). Their joint count is at most \(1+H/\operatorname{lcm}(q,d)\), including incompatible pairs. If \(g=\gcd(q,d)\), the map \((q,d)\mapsto(g,q/g,d/g)\) is injective, with reciprocal lcm equal to the reciprocal product of the three coordinates. Thus
\[
\sum_{n=u}^{u+H} F(n)^2
 \le Q^2+H\left(\sum_{i=1}^{Q}\frac1i\right)^3 .
\]
Cauchy–Schwarz bounds the square of the total selected-class count by \(|E|\) times this expression. Apply it to the previously proved global or interval count for theta exceptions. The term \(Q^2\) accounts for incomplete periods on the interval. [CRT and reciprocal lcm sum](ThetaProgressionIncidence.lean) · [Second moment](ThetaProgressionOccupancy.lean) · [Global exception theorem](MULTISCALE-PRIME-EXCEPTIONS.md)

## Every polynomially short interval

Let \(r=\sqrt{\log X\log\log X}\), \(v=r/16384\). In every interval \((X,X+H]\) with \(X^{3/4}e^{r/512}\le H\le X\), the sum over \(q\le Q\) of the worst-class counts is at most \((H/\log X)e^{-2v}\) whenever \(Q^2\le He^v\). This holds for \(S(p)\le c p\log p\) at every fixed \(c<1/2\), and for \(\lvert S(p)-\tfrac12 p\log p\rvert\ge\varepsilon p\log p\) at every fixed \(\varepsilon>0\). The threshold on \(X\) may depend on \(c\) or \(\varepsilon\). The proof uses the unconditional short-interval theorem for the unpartitioned sample. [Interval transfer and original-sum statements](ThetaShortIntervalClasses.lean) · [Underlying interval estimate](SHORT-PRIME-INTERVALS.md)

The DeepMind issue and OMA reductions compare the integer sum to pointwise remainder terms. The estimates above bound the total number of exceptions across independently selected arithmetic progressions. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [Left to Solve](https://www.lefttosolve.com/p/Arxiv.2501.03234.conjecture_4_2.R1.H1) · [OMA](https://github.com/lefttosolve2/open-math-agents/pull/34398)


## Direct comparison with the ordinary formal statement

At the pinned external commit, the Git blob for `Challenge.lean` is `8ff46aace0b8ca45f1b03b85a9ddd513a96298bd`. Take the unmodified definition prefix preceding the first `namespace BombieriVinogradov` as `ThetaExternalBVBoundary.lean`. The following comparison checks the ordinary proposition by reflexivity and gives the theta conclusion with its original real endpoints. The supplemental replay uses only that definition prefix. The proof of the ordinary theorem is a separate dependency. [Pinned definition source](https://github.com/kimihiro64/bombieri-vinogradov/blob/7a1748306e026825ed6a5555516cc2f28989b2ac/Challenge.lean) · [Proof entry point](https://github.com/kimihiro64/bombieri-vinogradov/blob/7a1748306e026825ed6a5555516cc2f28989b2ac/Solution.lean)

```lean
import ThetaRealPrimeClassBV
import ThetaExternalBVBoundary

/-! Compare against the unchanged ordinary counting definitions at the pinned source. -/
namespace ThetaPrimeClassBVComparison
open Arxiv.«2501.03234» Filter Real Finset

theorem same_statement : ThetaPrimeClassBV.Ordinary = _root_.BombieriVinogradov := rfl

theorem transfer (H : _root_.BombieriVinogradov) {θ A : ℝ} (hθ : θ<1/2) (hA : 1≤A) (k : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ X : ℕ in atTop,
      ∑ q∈Icc 1 ⌊(X:ℝ)^θ⌋₊,ThetaPrimeClassBV.error (ThetaPrimeClassBV.slopeCount k) X q ≤
        C*X/(log X)^A :=
  ThetaPrimeClassBV.slope H hθ hA k

theorem exact_real (H : _root_.BombieriVinogradov) (k : ℕ) :
    ∀ θ < (1/2:ℝ), ∀ A ≥ (1:ℝ), ∃ C > (0:ℝ), ∀ x ≥ (3:ℝ),
      ∑ q∈Icc 1 ⌊x^θ⌋₊, ⨆ a : (ZMod q)ˣ,
        |(ThetaPrimeClassBV.slopeCount k x q a : ℝ) - _root_.pi x / q.totient| ≤
          C*x/(log x)^A :=
  ThetaRealPrimeClassBV.slope H k

#print axioms exact_real
#print axioms same_statement
#print axioms transfer
end ThetaPrimeClassBVComparison
```
