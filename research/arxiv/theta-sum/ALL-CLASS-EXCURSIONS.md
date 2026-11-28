# Both prime tails in every reduced residue class

Put \(R(p)=S(p)/p-\tfrac12\log p\), and let \(B\) be its limiting prime mean. Fix \(q\ge1\) and \(0\le r<q\) with \((r,q)=1\). For each sufficiently large real \(b\) and all sufficiently large \(X\), each of the two sets
\[
 \{p\le X:p\equiv r\bmod q,\ R(p)>B+b\},\qquad
 \{p\le X:p\equiv r\bmod q,\ R(p)<B-b\}
\]
has at least \(\exp(-\exp(32\pi\sqrt b))\,\pi(X)\) elements. For every fixed real height both sets have positive lower density among all primes. The lower threshold for \(b\) may depend on \(q,r\), and the lower threshold for \(X\) may also depend on \(b\). This includes \(1\bmod8\). Both inequalities describe deviations on the scale of \(p\) around \(\tfrac12p\log p+Bp\). [Prime count](ThetaAllClassExcursions.lean) · [Dyadic classes and comparison](LARGE-PRIME-TAILS.md)

## Large means in compatible progressions

Write \(m=(T!)^T\) and \(D=\sum_{d\mid m}1/d\). Dirichlet's theorem supplies a large fixed odd prime \(a\equiv r^{-1}\bmod q\). If \(k=m/a^{v_a(m)}\), then \(a+k\) is a unit modulo \(m\). Its inverse \(n\) reduces to \(r\bmod q\) once \(q\mid m\), and \(n^{-1}\equiv a\bmod d\) for every \(d\mid m\) prime to \(a\). This construction includes the trivial modulus. [Compatible units](ThetaCompatibleUnits.lean)

For odd \(d\mid m\) prime to \(a\), the reciprocal wave agrees with the identity wave up to \(w<d/a\). Summation over one period and a uniform tail bound give a row contribution of at least \(U(d)-(4a+3)\), where \(U(d)\) sums \(1/w\) over the odd \(w\le d\) coprime to \(d\). Summing over coprime pairs of odd divisors gives \(\sum_{d\mid m,\ d\ \mathrm{odd}}U(d)/d\ge D^2/16\). For primes of \(m\) at most \(T\), the log-weighted divisor sum is at most \(D(1+4\log T)\). The denominators divisible by \(a\) therefore cost \(O(D^2/a)+O_a(D)\). Choosing \(a\) sufficiently large preserves a positive quadratic contribution. [Reciprocal rows](ThetaInverseResidueRows.lean) · [Divisor triangle and log moment](ThetaDivisorTriangle.lean) · [Captured-row inequality](ThetaCompatibleCapture.lean)

For all large \(T\), the centered conditional mean on some unit class modulo \(m\) above \(r\) is at least \((\log T)^2/(8\pi^2)\). Only odd characters contribute to the centered predictor, so its value changes sign at the opposite unit. Applying the construction above \(-r\) and reflecting gives a second unit class above \(r\) with mean at most \(-(\log T)^2/(8\pi^2)\). A global prime second moment converts both means to prime counts within \(r\bmod q\). The estimate \(\log m\le T^3\), followed by \(T=\lceil\exp(8\pi\sqrt b)\rceil\), gives the stated fraction. [Finite models](ThetaCompatibleModels.lean) · [Reflection](ThetaOppositeMeans.lean) · [Two conditional means](ThetaCompatibleMeans.lean) · [Localized second-moment argument](ThetaCompatibleCounts.lean)

## Original sum and replay

The pinned DeepMind positivity statement asks for the sign of \(S(p)\) at each prime under its hypotheses. The paper also asks for eventual lower and upper growth bounds. The counts here concern extreme values of the centered residual in specified prime classes. The pointwise sign and the eventual lower inequality remain open. [Original paper, Conjectures 1.1 and 3.3](https://arxiv.org/pdf/2501.03234v3) · [Pinned definition and conjectures](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean) · [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA harmonic estimate](https://github.com/lefttosolve2/open-math-agents/pull/22818) · [Left to Solve](https://lefttosolve.com/api/solved)

The even continued-fraction approach has open proof submissions for the integral mean and fixed-depth grid limit. Its parent reduction also needs uniform control of prefix overshoot. [Parent reduction](https://github.com/lefttosolve2/open-math-agents/pull/21388) · [Integral mean](https://github.com/lefttosolve2/open-math-agents/pull/27960) · [Grid limit](https://github.com/lefttosolve2/open-math-agents/pull/28015)

The following bridge supplies the fixed-progression prime number theorem. [Pinned PNT source and replay](NATURAL-PRIME-MEAN.md#joint-lean-replay)

```lean
import ThetaAllClassExcursions
import ThetaPNTCorollaries

/-! Opposite excursions of the original prime residual in every reduced class. -/
namespace Arxiv.«2501.03234».ThetaAllClassExcursionsPNT
open Finset Filter Real ThetaPrimeDensity ThetaDiagonalConstant

theorem counts {q r : ℕ} (hq : 0 < q)
    (hr : r < q) (hc : r.Coprime q) :
    ∀ᶠ b : ℝ in atTop, ∀ᶠ X : ℕ in atTop,
      let d := exp (-(exp (32*Real.pi*sqrt b)))*X.primeCounting
      d ≤ ((primeSet (fun p => p%q=r ∧ diagonalConstant+b<(S p:ℝ)/p-log p/2) X).card:ℝ) ∧
      d ≤ ((primeSet (fun p => p%q=r ∧ (S p:ℝ)/p-log p/2<diagonalConstant-b) X).card:ℝ) :=
  ThetaAllClassExcursions.counts ThetaPNTCorollaries.progression_mangoldt hq hr hc

theorem every_height {q r : ℕ} (hq : 0 < q)
    (hr : r < q) (hc : r.Coprime q) (b : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ X : ℕ in atTop,
      δ*X.primeCounting ≤ ((primeSet (fun p => p%q=r ∧ diagonalConstant+b<(S p:ℝ)/p-log p/2) X).card:ℝ) ∧
      δ*X.primeCounting ≤ ((primeSet (fun p => p%q=r ∧ (S p:ℝ)/p-log p/2<diagonalConstant-b) X).card:ℝ) :=
  ThetaAllClassExcursions.every_height ThetaPNTCorollaries.progression_mangoldt hq hr hc b

#print axioms counts
#print axioms every_height
end Arxiv.«2501.03234».ThetaAllClassExcursionsPNT
```
