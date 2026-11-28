# Opposite second coefficients on primes modulo three

Let $R(p)=S(p)/p-\tfrac12\log p$ for the original integer theta sum. Write $B$ for its ordinary mean over all primes, about $0.2399341$, and $\pi_r(X)$ for the number of primes $p\le X$ with $p\equiv r\pmod3$. There is a constant $C$ such that

\[
  \lim_{X\to\infty}\frac{1}{\pi_1(X)}
     \sum_{\substack{p\le X\\p\equiv1\ (3)}}R(p)=B+C,\qquad
  \lim_{X\to\infty}\frac{1}{\pi_2(X)}
     \sum_{\substack{p\le X\\p\equiv2\ (3)}}R(p)=B-C,
  \qquad C\ge\frac{968}{375\pi^2}>0.261.
\]

Each average uses its own class size. In particular, at every sufficiently large endpoint the first average is greater than $261/1000$ and the second is less than $-1/500$. The offset $C$ is also the ordinary prime mean of $\chi_3(p)R(p)$, where $\chi_3$ takes values $0,1,-1$ on $0,1,2\bmod3$. [Class means, twist and strict margins](ThetaCharacterPrimeMeans.lean) · [All-prime mean and series for B](NATURAL-PRIME-MEAN.md)

The variance over all primes has a finite, strictly positive limit. If $\overline R_X$ is the average of $R$ over the $\pi(X)$ primes up to $X$, then for the same $C$ there is a real $V$ with
\[
  \lim_{X\to\infty}\frac{1}{\pi(X)}\sum_{p\le X}(R(p)-\overline R_X)^2
  =\lim_{X\to\infty}\frac{1}{\pi(X)}\sum_{p\le X}(R(p)-B)^2
  = V \ge C^2 \ge \left(\frac{968}{375\pi^2}\right)^2 > 0.0684.
\]
This gives a limit and an explicit lower bound for the second moment previously bounded above. The [subsequent Euler product](EXACT-MOD-THREE-BIAS.md) evaluates $C$. The exact value of $V$ remains open. The signs concern the **mean residual after subtracting the half-log term**. The pointwise conjecture $S(p)>0$ at every odd prime remains open. [Limiting variance](ThetaCharacterPrimeMeans.lean) · [Earlier finite upper bound](PRIME-VARIANCE.md)

## How the character enters

The scaled off-diagonal of $S(p)$ has finite periodic models with arbitrarily small mean absolute error over primes. Multiplication by $\chi_3$ preserves this error estimate. Each fixed model has a mean over primes given by its average on the units of its period. The twisted mean is nonnegative in each primitive denominator, and denominator three alone contributes at least $(4/15)(121/100)$. Approximating by these convergent finite means shows that the full twisted mean converges. The scaling back to $R$ contributes $8/\pi^2$. [Finite character transform](ThetaCharacterThree.lean) · [Signs of the twisted row means](ThetaConditionalRows.lean) · [Prime approximation](ThetaPrimeTailTransfer.lean)

The contribution of the centered diagonal to this twist vanishes because the diagonal tends to $B$ and $|\chi_3|\le1$. The constant diagonal term also vanishes in the twisted mean. At every prime above three the indicators of the two classes are $(1\pm\chi_3)/2$. Each class has density $1/2$ among primes, which accounts for the normalization in the two limits. [Ordinary prime equidistribution](ThetaNaturalPrimeMeans.lean) · [Pointwise diagonal limit](ThetaDiagonalConstant.lean)

For the variance, the difference between the root mean squares of two functions is bounded by the root mean square of their difference. The finite models approximate the scaled off-diagonal in this stronger norm too, and their squared values have ordinary prime means by periodicity. The full root mean square is therefore Cauchy. The centered diagonal has vanishing root mean square. Finally, testing $R-B$ against $\chi_3$ gives $C^2\le V$, and the prime mean of $R$ tending to $B$ identifies the empirical and fixed-center variances. [Root mean square transfer and recentering](ThetaCharacterPrimeMeans.lean)

## Source comparison

Berndt, Bhat, Meyer, Xie and Zaharescu study the aggregate $S(k)$ and conjecture pointwise growth on primes. Their Section 5 asymptotic treats a divisor sum related to $T(k)$. Lägeler studies modular distribution of individual Hardy sums. Here the random variable is the signed aggregate at a prime denominator. The live DeepMind reduction expresses pointwise inequalities via a row remainder. The OMA reductions for $2p<S(p)$ and for eventual growth retain additional hypotheses. The LTS entry concerns an odd harmonic estimate. [Paper](https://arxiv.org/pdf/2501.03234v3) · [Pinned integer predicate](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean) · [Lägeler](https://arxiv.org/abs/2207.04828) · [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA harmonic reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/21541) · [OMA continued fractions](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/21388) · [LTS-listed step](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7126)

## Joint Lean replay

The notebook proves the transfers under `ProgressionMangoldt`. The combined module below imports the earlier progression theorem from its joint replay with PrimeNumberTheoremAnd, pinned at `55270df807213fc3584523d09e0311d7dc073ff5` on Lean 4.33.1. Both conclusions below are unconditional. [Previous joint module and environment setup](NATURAL-PRIME-MEAN.md#joint-lean-replay) · [Upstream progression theorem](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/55270df807213fc3584523d09e0311d7dc073ff5/PrimeNumberTheoremAnd/Wiener.lean#L4025-L4051)

```lean
import ThetaCharacterPrimeMeans
import ThetaPNTCorollaries

/-! Character-separated prime means and limiting variance with the PNT input discharged. -/
namespace Arxiv.«2501.03234».ThetaCharacterPNT

open Filter ThetaPNTCorollaries ThetaCharacterPrimeMeans ThetaNaturalPrimeMeans ThetaDiagonalConstant
open scoped Topology

theorem class_statistics :
    ∃ C V : ℝ, 968/(375*Real.pi^2) ≤ C ∧ C^2 ≤ V ∧
      Tendsto (classMean 1 residual) atTop (𝓝 (diagonalConstant+C)) ∧
      Tendsto (classMean 2 residual) atTop (𝓝 (diagonalConstant-C)) ∧
      Tendsto (primeMean (fun p => (residual p-diagonalConstant)^2)) atTop (𝓝 V) ∧
      Tendsto (sampleVariance residual) atTop (𝓝 V) :=
  S_prime_class_statistics progression_mangoldt

theorem class_mean_signs :
    ∀ᶠ X : ℕ in atTop, 261/1000 < classMean 1 residual X ∧
      classMean 2 residual X < -(1/500) :=
  S_class_mean_signs progression_mangoldt

#print axioms class_statistics
#print axioms class_mean_signs

end Arxiv.«2501.03234».ThetaCharacterPNT
```

After building `ThetaPNTCorollaries` as in the preceding note, reuse its `bridge_dir`, `pnt_path` and notebook olean directory, including `ThetaCharacterPrimeMeans.olean`. From the Formal Conjectures checkout run

```sh
awk '/^```lean$/ { lean = 1; next } lean && /^```$/ { exit } lean { print }' \
  "$NOTEBOOK/research/arxiv/theta-sum/MOD-THREE-PRIME-MEANS.md" > "$bridge_dir/ThetaCharacterPNT.lean"
lake env sh -ec '
  export LEAN_PATH="$1:$2:$3:$LEAN_PATH"
  cd "$1"
  lean -o ThetaCharacterPNT.olean ThetaCharacterPNT.lean
  leanchecker -v ThetaCharacterPNT
' sh "$bridge_dir" "$THETA_OLEANS" "$pnt_path"
```

The axiom reports for both conclusions contain only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the derivation and formalization. [Notebook replay](../../README.md)
