# Quantitative lower bounds for both tails of the prime theta residual

Let $R(p)=S(p)/p-\frac12\log p$ for the original integer theta sum and let $B$ denote its limiting ordinary prime mean. For every sufficiently large real $b$, **each** open tail of the limiting law beyond $B\pm b$ has probability at least
\[
e(b)=\exp\!\left[-\exp(32\pi\sqrt b)\right].
\]
For every reduced class $r\bmod 2^k$, both counts
\[
\#\{p\le X:p\equiv r\ (2^k),\ R(p)>B+b\},\qquad
\#\{p\le X:p\equiv r\ (2^k),\ R(p)<B-b\}
\]
are at least $e(b)\pi(X)/(4\varphi(2^k))$ for all sufficiently large $X$. The height threshold is uniform in the dyadic class. The prime endpoint may depend on $b,k,r$. This is a lower bound for the tail, with no claim of a matching upper bound or effective prime endpoint. [Original Lean sum](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean) · [Prime counts](ThetaLargePrimeTails.lean) · [Limiting probability](ThetaLargeLawTails.lean)

The constructive class-mean result uses the prescribed modulus $m_T=(T!)^T$. For **every sufficiently large integer $T$**, the mean of $R(p)$ over primes $p\equiv1\pmod{m_T}$ converges and is at least
\[
B+\frac{(\log T)^2}{16\pi^2}.
\]
Here $T$ is fixed before taking the prime limit. This strengthens the earlier existence of identity classes of arbitrarily large mean. [Class means](ThetaLargeIdentityMeans.lean) · [Earlier unbounded excursions](UNBOUNDED-EXCURSIONS.md)

## Lower bound for the captured rows

For odd $d>1$, let $U(d)=\sum_{w\le d,\ w\text{ odd},\ (w,d)=1}1/w$. In the identity class the first $d$ terms of the reciprocal row sum to $U(d)$. If $A_n$ is the prefix sum of the signs, then $A_n\ge0$ and $A_d\le d$. Subtracting $A_n/(n+1)$ from the weighted row produces a nondecreasing sequence. Thus every cutoff $K\ge d$ has row at least $U(d)-1$. Combining this with the earlier lower bound $1/2$ retains a positive contribution even when the first harmonic estimate is small. [First-half row bound](ThetaIdentityHarmonics.lean)

Let $H_o(T)$ be the harmonic mass of the positive odd integers through $T$. In the odd square $w,d\le T$, pairs with a common prime divisor have reciprocal weight at most $H_o(T)^2\sum_{n\ge3}1/n^2\le H_o(T)^2/2$. Division by each common odd prime preserves oddness and bounds the mass of its multiples by $H_o(T)/p$. Swapping the two coordinates retains at least half the coprime mass in the triangle $w\le d$. Consequently $\sum_{d\le T,\,d\text{ odd}} U(d)/d\ge H_o(T)^2/4$, and $H_o(T)\ge H_T/2$. [Coprime harmonic triangle](ThetaOddHarmonicTriangle.lean)

All denominators $d\le T$ divide $m_T$. The remaining off-divisor error is $o(D(m_T))$, uniformly in the model cutoffs, where $D(m)=\sum_{d\mid m}1/d$. The earlier smooth-divisor estimate applies with $A=T$, since every fixed power of $T$ divided by $2^T$ tends to zero. Half the uniform identity-row contribution absorbs this entire error. The coprime triangle then leaves a model mean at least $(H_o(T)^2/4-H_o(T))/2-1/4$. The factor $8/\pi^2$ in the transfer to $S(p)$ gives the stated class-mean bound. [Factorial sequence](ThetaFactorialSequence.lean) · [Finite class means](ThetaLargeIdentityModels.lean)

## From class means to tail probabilities

The centered second prime moment is eventually bounded by a constant. On the identity class, the prime mean exceeds $B+(\log T)^2/(32\pi^2)+1$ for large $T$. Cauchy–Schwarz gives an all-prime fraction at least $1/(C m_T^2)$ above the smaller threshold, with a single constant $C$ independent of $T$. Closed half-lines transfer this bound to the limiting law. Taking $T=\lceil\exp(8\pi\sqrt b)\rceil$ puts the threshold strictly beyond $B+b$. The elementary inequality $\log m_T\le T^3$ gives $C m_T^2\le\exp(\exp(32\pi\sqrt b))$ eventually. Reflection about $B$ supplies the opposite tail. Weak convergence inside each fixed dyadic class then gives the two ordinary prime counts. [Second moment and finite prime count](ThetaClassTailSize.lean) · [Law transfer](ThetaLargeLawTails.lean)

## Scope and replay

The paper's pointwise sign and eventual lower conjectures remain open. The variable $b$ is the height of a fluctuation about $\frac12p\log p+Bp$ on the scale $p$. The DeepMind and OMA entries treat sign reductions or finite cases. Bettin's cotangent distribution concerns $c_0(a/q)$ averaged over numerators. The bounds here concern the aggregate $S(p)$ with variable prime denominator. [Berndt et al., section 3](https://arxiv.org/pdf/2501.03234v3#page=4) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA reduction](https://github.com/lefttosolve2/open-math-agents/pull/22818) · [LTS feed](https://lefttosolve.com/api/solved) · [Bettin](https://arxiv.org/abs/1411.2293)

The joint module discharges the progression hypothesis using the pinned prime number theorem. [Joint replay instructions](NATURAL-PRIME-MEAN.md#joint-lean-replay)

```lean
import ThetaPNTCorollaries
import ThetaLargePrimeTails

/-! Quantitative prime excursions with the progression theorem discharged. -/
namespace Arxiv.«2501.03234».ThetaLargePrimeTailsPNT
open Filter MeasureTheory ThetaPrimeLaw ThetaProfiniteUnits ThetaNaturalPrimeMeans
open ThetaDiagonalConstant ThetaPrimeDensity ThetaFactorialSequence ThetaDyadicLaw
open scoped Topology

theorem identity_means : ∀ᶠ T : ℕ in atTop, ∃ L : ℝ,
    diagonalConstant+(Real.log T)^2/(16*Real.pi^2) ≤ L ∧
    Tendsto (progressionMean (modulus T) 1 (fun p => (S p:ℝ)/p-Real.log p/2)) atTop (𝓝 L) :=
  ThetaLargeIdentityMeans.means ThetaPNTCorollaries.progression_mangoldt

theorem prime_tails : ∀ᶠ b : ℝ in atTop,
    ∀ k r : ℕ, r.Coprime (2^k) → r<2^k → ∀ᶠ X : ℕ in atTop,
      let d := Real.exp (-(Real.exp (32*Real.pi*Real.sqrt b)))/(4*((2^k).totient:ℝ))
      d*X.primeCounting ≤ ((primeSet (fun p => p%2^k=r ∧ diagonalConstant+b<(S p:ℝ)/p-Real.log p/2) X).card:ℝ) ∧
      d*X.primeCounting ≤ ((primeSet (fun p => p%2^k=r ∧ (S p:ℝ)/p-Real.log p/2< diagonalConstant-b) X).card:ℝ) :=
  ThetaLargePrimeTails.counts ThetaPNTCorollaries.progression_mangoldt

theorem limiting_tails : ∀ᶠ b : ℝ in atTop, ∀ F : G →₁[haar] ℝ,
    Represents (fun p => (S p:ℝ)/p-Real.log p/2) F →
    let e := ENNReal.ofReal (Real.exp (-(Real.exp (32*Real.pi*Real.sqrt b))))
    e ≤ (haarLaw F : Measure ℝ) (Set.Ioi (diagonalConstant+b)) ∧
    e ≤ (haarLaw F : Measure ℝ) (Set.Iio (diagonalConstant-b)) :=
  ThetaLargeLawTails.tails ThetaPNTCorollaries.progression_mangoldt

#print axioms identity_means
#print axioms prime_tails
#print axioms limiting_tails
end Arxiv.«2501.03234».ThetaLargePrimeTailsPNT
```
