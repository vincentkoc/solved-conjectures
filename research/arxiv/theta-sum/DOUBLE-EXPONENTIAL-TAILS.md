# Double-exponential tails for the original prime theta residual

Write \(R(p)=S(p)/p-\tfrac12\log p\) and let \(B\) be its limiting mean over the primes. There is an absolute \(c>0\) such that for every sufficiently large **fixed** \(b\), all sufficiently large \(X\) satisfy
\[
 \frac{\#\{p\le X:p\text{ prime},\ |R(p)-B|>b\}}{\pi(X)}
 \le \exp\!\big(-\exp(c\sqrt b)\big).
\]
The lower threshold on \(X\) may depend on \(b\). This bounds excursions of the secondary term in the original sum. Positivity of \(S(p)\) for every odd prime remains open. [Original-sum prime count](ThetaDoubleExponentialTails.lean) · [Berndt–Bhat–Meyer–Xie–Zaharescu](https://arxiv.org/abs/2501.03234) · [Pinned DeepMind declarations](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean)

The bounds also hold for finite counts within any fixed reduced progression \(p\equiv r\pmod q\). Normalize by the number of primes in that progression through \(X\), and write \(Y(p)=R(p)-B\). For all sufficiently large \(b\), then all sufficiently large \(X\), the proportions with \(Y(p)>b\) and \(Y(p)<-b\) are each at least \(\tfrac12\varphi(q)\exp(-\exp(32\pi\sqrt b))\). The proportion with \(\lvert Y(p)\rvert>b\) is at most \(2\varphi(q)\exp(-\exp(c\sqrt b))\). The lower fractions use the [prime excursion counts](ALL-CLASS-EXCURSIONS.md) together with the asymptotic class size. The upper bound follows by comparing the class count with the total. [Counts within a reduced progression](ThetaClassTailCounts.lean)

For \(q=2^k\), the height threshold can be chosen **before** \(k,r\). The two lower bounds hold with prefactor \(1/2\), and the combined upper bound, including equality at \(b\), holds with prefactor \(2\) and an absolute positive exponent constant. The endpoint \(X\) may still depend on \(k,r,b\). The proof uses the common dyadic law, open one-sided tails for the lower estimates, and a closed outer tail contained in the open tail at \(b/4\) for the upper estimate. This includes \(1\bmod8\). [Dyadic counts](ThetaDyadicTailCounts.lean)

For the limiting probability law \(\mu\) of \(R\), the same upper bound holds for the mass outside \([B-b,B+b]\). Each of \((B+b,\infty)\) and \((-\infty,B-b)\) has mass at least \(\exp(-\exp(32\pi\sqrt b))\) for all sufficiently large \(b\). Thus for either one-sided tail of mass \(P_b\), \(\log\log(1/P_b)\asymp\sqrt b\). The constants inside the second exponential need not agree. [Two-sided theorem](ThetaDoubleExponentialLaw.lean) · [Lower tail masses](ThetaLargeLawTails.lean)

For \(M_k=\lim_{X\to\infty}\pi(X)^{-1}\sum_{p\le X}|R(p)-B|^k\), the same proof gives
\[
 a(\log k)^2\le M_k^{1/k}\le C(\log k)^2
\]
for absolute \(a,C>0\) and all sufficiently large integers \(k\). Every fixed reduced class modulo a power of two has the same limiting moment \(M_k\). Here \(k\) is fixed while taking the prime limit. For the lower estimate, use the positive tail at \(b=(\log k/(32\pi))^2\), where its probability is at least \(e^{-k}\). For the upper estimate, take \(b=(2\log k/c)^2\). The variable \(U=k\log\max(1,|R-B|/b)\) has tail at most \(e^{-2t}\) for \(t\ge0\), giving \(\mathbb E e^U\le2\) by integration. [Moment bounds](ThetaTailMomentScale.lean) · [Original prime and dyadic limits](ThetaSharpPrimeMoments.lean)

## Revealing prime powers

Average a finite reciprocal-row model over the units modulo \(Y!\). Reveal the full prime powers of \(Y!\) in increasing order of their base prime. At a cutoff \(T\), the conditional mean on any reduced class has absolute value \(O((\log T)^2)\), uniformly in \(Y\) and the smoothing parameter. This uses reciprocal divisor mass and its logarithmic moment for integers supported on primes at most \(T\), without any bound on their exponents. [Smooth conditional means](ThetaSmoothConditionalModel.lean) · [Divisor estimates](ThetaDivisorBudget.lean)

Revealing \(q^{v_q(Y!)}\) changes the conditional means of sibling classes by at most \(C(\log q)^2/q\). A row of denominator \(d\) agrees on both classes if \(q\nmid d\). Otherwise \(q\) divides \(\gcd(d,m)\) for the newly exposed modulus \(m\), so the logarithmically weighted sum over divisors gains the required factor. The estimate holds for every exponent. [Coordinate oscillation](ThetaPrimeCoordinate.lean) · [Unit-fiber averaging](ThetaUnitExposure.lean)

At tilt \(v=\pm T^{1/4}\), the charge for a prime \(q>T\) is at most \(q^{-5/4}\) once \(T\) is large. The sum of these charges is bounded independently of \(T\) and \(Y\). An exponential moment estimate on the finite partitions and Markov's inequality therefore give a tail of size \(2\exp(C_0-T^{1/4})\) at height \(1+C_1(\log T)^2\). Periodic prime averages and the prime mean absolute approximation to \(R\) transfer this to an eventual finite prime count. Taking \(T\) of order \(\exp(c_0\sqrt b)\) gives the stated bound. [Finite exponential moment](ThetaModelExponentialMoment.lean) · [Transfer to primes](ThetaPrimeTailCutoff.lean)

The DeepMind reduction and the OMA work on H1 and H2 address pointwise estimates. Lägeler gives a continued-fraction formula and a graph-density result for individual Hardy sums. The distribution here is over prime denominators after summing over every numerator. [Lägeler](https://arxiv.org/abs/2203.09834) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA H1](https://github.com/lefttosolve2/open-math-agents/pull/27960) · [OMA H2](https://github.com/lefttosolve2/open-math-agents/pull/28015)

## Exact declarations with progression PNT discharged

The following bridge uses the progression PNT at the pinned external revision. [PNT source and replay](NATURAL-PRIME-MEAN.md#joint-lean-replay)

```lean
import ThetaSharpPrimeMoments
import ThetaPNTCorollaries

/-! Double-exponential prime counts and limiting masses with progression PNT discharged. -/
namespace Arxiv.«2501.03234».ThetaDoubleExponentialPNT
open Real Filter Finset MeasureTheory ThetaPrimeDensity ThetaPrimeLaw ThetaProfiniteUnits
open ThetaDiagonalConstant ThetaCharacterPrimeMeans
noncomputable section

theorem prime_count : ∃ c : ℝ, 0<c ∧ ∀ᶠ b : ℝ in atTop, ∀ᶠ X : ℕ in atTop,
    ((primeSet (fun p => b < |(S p:ℝ)/p-log p/2-diagonalConstant|) X).card:ℝ)/X.primeCounting ≤
      exp (-exp (c*sqrt b)) :=
  ThetaDoubleExponentialTails.original_prime ThetaPNTCorollaries.progression_mangoldt

theorem law_tails : ∃ c : ℝ, 0<c ∧ ∀ᶠ b : ℝ in atTop, ∀ F : G →₁[haar] ℝ, Represents residual F →
    let μ := (haarLaw F : Measure ℝ)
    let lower := ENNReal.ofReal (exp (-exp (32*π*sqrt b)))
    lower ≤ μ (Set.Ioi (diagonalConstant+b)) ∧ lower ≤ μ (Set.Iio (diagonalConstant-b)) ∧
      μ (ThetaDoubleExponentialLaw.outside b) ≤ ENNReal.ofReal (exp (-exp (c*sqrt b))) :=
  ThetaDoubleExponentialLaw.two_sided ThetaPNTCorollaries.progression_mangoldt

theorem prime_moments : ∃ a C : ℝ, 0<a ∧ 0<C ∧ ∀ᶠ k : ℕ in atTop,
    ∃ M : ℝ, (a*(log k)^2)^k≤M ∧ M≤(C*(log k)^2)^k ∧
      Tendsto (ThetaNaturalPrimeMeans.primeMean (fun p => |(S p:ℝ)/p-log p/2-diagonalConstant|^k))
        atTop (nhds M) ∧
      ∀ l r : ℕ, r.Coprime (2^l) → r < 2^l →
        Tendsto (ThetaDyadicLaw.progressionMean (2^l) r (fun p => |(S p:ℝ)/p-log p/2-diagonalConstant|^k))
          atTop (nhds M) :=
  ThetaSharpPrimeMoments.original ThetaPNTCorollaries.progression_mangoldt

#print axioms prime_moments
#print axioms prime_count
#print axioms law_tails
end
end Arxiv.«2501.03234».ThetaDoubleExponentialPNT
```

The following joint module specializes both class counts to the pinned progression PNT.

```lean
import ThetaClassTailCounts
import ThetaPNTCorollaries

/-! Matching tail counts for the original prime sum, with progression PNT discharged. -/
namespace Arxiv.«2501.03234».ThetaClassTailCountsPNT
open Real Filter ThetaDiagonalConstant ThetaDyadicTailCounts

theorem classes : ∃ c : ℝ, 0<c ∧
    ∀ q r : ℕ, 0<q → r<q → r.Coprime q → ∀ᶠ b : ℝ in atTop, ∀ᶠ X : ℕ in atTop,
      let l := (q.totient:ℝ)/2*exp (-exp (32*π*sqrt b))
      let R := fun p : ℕ => (S p:ℝ)/p-log p/2-diagonalConstant
      l≤fraction q r X (fun p => b<R p) ∧ l≤fraction q r X (fun p => R p< -b) ∧
        fraction q r X (fun p => b < |R p|)≤2*q.totient*exp (-exp (c*sqrt b)) :=
  ThetaClassTailCounts.original ThetaPNTCorollaries.progression_mangoldt

theorem dyadic : ∃ c : ℝ, 0<c ∧ ∀ᶠ b : ℝ in atTop, ∀ k r : ℕ,
    r.Coprime (2^k) → r<2^k → ∀ᶠ X : ℕ in atTop,
      let l := exp (-exp (32*π*sqrt b))/2
      let R := fun p : ℕ => (S p:ℝ)/p-log p/2-diagonalConstant
      l≤fraction (2^k) r X (fun p => b<R p) ∧ l≤fraction (2^k) r X (fun p => R p< -b) ∧
        fraction (2^k) r X (fun p => b≤|R p|)≤2*exp (-exp (c*sqrt b)) :=
  ThetaDyadicTailCounts.original ThetaPNTCorollaries.progression_mangoldt

#print axioms classes
#print axioms dyadic
end Arxiv.«2501.03234».ThetaClassTailCountsPNT
```
