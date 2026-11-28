# Which congruence periods approximate the theta sum at primes?

Let $R(p)=S(p)/p-\tfrac12\log p$ and let $(m_j)$ be any prescribed sequence of positive integers. There exist real functions $g_j$ modulo $m_j$ satisfying
\[
 \forall\varepsilon>0,\quad\forall j\text{ sufficiently large},\quad
 \forall X\text{ sufficiently large},\qquad
 \frac1{\pi(X)}\sum_{p\le X}|R(p)-g_j(p)|\le\varepsilon
\]
**if and only if each fixed odd integer eventually divides $m_j$**. The same equivalence holds when the primes are restricted to any fixed reduced class $a\bmod 2^k$ and the denominator is the number of primes in that class. Each $g_j$ is chosen independently of $\varepsilon$ and $X$. The cutoff in $X$ may depend on $j$ and $\varepsilon$. [All primes](ThetaModelPeriods.lean) · [Dyadic progression theorem](ThetaDyadicSpectrum.lean) · [Original theta sum and prime conjectures](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean)

In particular the odd parts of $j!$ furnish admissible periods. The products of the first $j$ odd primes fail at modulus nine, even though they eventually contain every odd prime. For any fixed squarefree $m$ and any real $g$ modulo $m$, all sufficiently large $X$ satisfy
\[
 \frac{\sum_{p\le X,\ p\equiv1\ (8)}|R(p)-g(p)|}
 {\#\{p\le X:p\equiv1\ (8)\}}>\frac1{32}.
\]
This identifies a limitation of congruence models within the $1\bmod8$ class where the pointwise positivity question is especially sharp. It gives an absolute-error bound and leaves the sign at an individual exceptional prime open. [Quantitative gap](ThetaDyadicSpectrum.lean) · [Modulus-nine coefficient](PRIMITIVE-SPECTRUM.md)

## Why every odd prime power is necessary

Fix an odd prime $p$ and $q=p^{b+1}$. Reduction of the unit group from $q$ to $p^b$ has a nontrivial kernel, since the Euler totient strictly decreases. Choose a nonidentity element $u$ in this kernel. Finite characters separate $u$ from $1$ and also separate $-1$ from $1$. If the character detecting $u$ is even, an odd character either already detects $u$ or is trivial there and can be multiplied into the detecting character. The resulting odd character does not factor through $p^b$, so its conductor is $q$. [Prime-power character witness](ThetaPrimePowerDigit.lean)

Its limiting correlation $C_\chi$ with $R$ is nonzero. If $q\nmid m$, the character annihilates every mod-$m$ model. Therefore each such model eventually has mean absolute error greater than $|C_\chi|/2$. This threshold depends on the missing precision $q$ and is uniform over all the periods and models missing it. Each odd integer has finitely many prime-power divisors, so sufficiently accurate late models force eventual divisibility by the entire integer. [Complete primitive spectrum](PRIMITIVE-SPECTRUM.md) · [Necessity and sufficiency](ThetaModelPeriods.lean)

Conversely, the reciprocal-row approximations already produce one odd-period model at every desired accuracy. A late period divisible by that odd period supports the same model. A diagonal choice of accuracies gives one family $g_j$ satisfying every tolerance. [Odd periods of the reciprocal model](ThetaDyadicLaw.lean) · [Prime approximation](ThetaPrimeResidualLaw.lean)

For a reduced dyadic class, the real and imaginary parts of an odd-conductor character have odd period. The joint dyadic restriction theorem preserves each component of the correlation with $R$ in the class. For a mod-$m$ model, class selection multiplies its period by at most $2^k$. This cannot restore a missing odd prime-power conductor. Dividing by the positive class density proves the same lower bound with the class count in the denominator. Positive density also transfers the upper approximation error from all primes. [Dyadic restriction](DYADIC-PRIME-LAW.md) · [Class correlation and error](ThetaDyadicSpectrum.lean)

## Source comparison and joint replay

The original paper asks for pointwise positivity and growth. The DeepMind and OMA entries give other reductions, bounds and finite checks. Guo and Zhang expand Hardy sums at a fixed prime denominator. The present criterion concerns families of congruence models for the original aggregate while its prime denominator varies. [Berndt et al., §3](https://arxiv.org/pdf/2501.03234v3#page=4) · [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA harmonic step](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7126) · [OMA finite bound](https://github.com/lefttosolve2/open-math-agents/pull/18042) · [LTS feed](https://lefttosolve.com/api/solved) · [Guo and Zhang, Lemma 4](https://dml.cz/dmlcz/141636)

The notebook theorems take the prime number theorem in fixed progressions as input. Save the following module as `ThetaModelPeriodsPNT.lean` on the joint replay path. Its three unconditional statements print only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the derivation and verification. [PNT source and replay](NATURAL-PRIME-MEAN.md#joint-lean-replay)

```lean
import ThetaDyadicSpectrum
import ThetaPNTCorollaries

/-! Prime-mean approximation with prescribed periods, on all primes and on dyadic classes. -/
namespace Arxiv.«2501.03234».ThetaModelPeriodsPNT
open Filter ThetaNaturalPrimeMeans ThetaPeriodMeans ThetaDyadicLaw

theorem prime_models {m : ℕ → ℕ} (hm : ∀ j, 0 < m j) :
    (∃ g : ℕ → ℕ → ℝ, (∀ j, OnMod (m j) (g j)) ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j in atTop, ∀ᶠ X in atTop,
        primeMean (fun p => |(S p : ℝ) / p - Real.log p / 2 - g j p|) X ≤ ε) ↔
    ∀ q : ℕ, Odd q → ∀ᶠ j in atTop, q ∣ m j :=
  ThetaModelPeriods.fixed_models_iff hm ThetaPNTCorollaries.progression_mangoldt

theorem dyadic_models {m : ℕ → ℕ} (hm : ∀ j, 0 < m j) {k a : ℕ}
    (ha : a.Coprime (2^k)) (hlt : a < 2^k) :
    (∃ g : ℕ → ℕ → ℝ, (∀ j, OnMod (m j) (g j)) ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j in atTop, ∀ᶠ X in atTop,
        progressionMean (2^k) a (fun p => |(S p : ℝ) / p - Real.log p / 2 - g j p|) X ≤ ε) ↔
    ∀ q : ℕ, Odd q → ∀ᶠ j in atTop, q ∣ m j :=
  ThetaDyadicSpectrum.fixed_class_models_iff hm ha hlt ThetaPNTCorollaries.progression_mangoldt

theorem one_mod_eight {m : ℕ} [NeZero m] (hm : Squarefree m) {g : ℕ → ℝ} (hg : OnMod m g) :
    ∀ᶠ X in atTop, 1 / 32 < progressionMean 8 1 (fun p => |(S p : ℝ) / p - Real.log p / 2 - g p|) X :=
  ThetaDyadicSpectrum.one_mod_eight_squarefree_gap hm ThetaPNTCorollaries.progression_mangoldt hg

#print axioms prime_models
#print axioms dyadic_models
#print axioms one_mod_eight
end Arxiv.«2501.03234».ThetaModelPeriodsPNT
```
