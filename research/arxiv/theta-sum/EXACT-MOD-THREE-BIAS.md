# Exact modulo-three bias of the theta sum over primes

For the integer theta sum $S$ of Berndt, Bhat, Meyer, Xie and Zaharescu, let $R(p)=S(p)/p-\tfrac12\log p$. Let $B$ denote its ordinary mean over all primes. For $r=1,2$, write $\pi_r(X)$ for the number of primes $p\le X$ with $p\equiv r\bmod3$. Then
\[
 \lim_{X\to\infty}\frac{1}{\pi_r(X)}
       \sum_{\substack{p\le X\\p\equiv r\bmod3}}R(p)
   = B+\chi_3(r) C,\qquad
 C=\frac{3\pi}{16\sqrt3}
   \prod_{\substack{\ell\ {\rm prime}\\\ell\equiv5\bmod6}}
      \left(1+\frac{2}{(\ell-1)^2}\right).
\]
Here $\chi_3$ is the real nonprincipal character modulo three. The ordinary prime mean of $\chi_3(p)R(p)$ also equals $C$. The limiting empirical variance $V$ from the preceding result satisfies $V\ge C^2$. Its exact value and the pointwise positivity conjecture for every odd prime remain open. [Exact Lean transfers](ThetaCharacterCoefficient.lean) · [Canonical integer sum](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean) · [Series for B](NATURAL-PRIME-MEAN.md) · [Previous class bounds and variance](MOD-THREE-PRIME-MEANS.md)

Numerically $C\approx0.398484$, so the class means differ by about $0.796968$ and $C^2\approx0.15879$. Truncating at $Y=10^6$ gives $0.3984839435$ for $C$ before the tail. For integer $Y>1$ the multiplicative tail lies between $1$ and $\exp(2/(Y-1))$, by $\log(1+x)\le x$ and the integral bound for $\sum_{n\ge Y}n^{-2}$. The decimals are numerical evaluations of the exact expression.

## Derivation

For every tolerance, the earlier prime mean-square model now works for every sufficiently large denominator cutoff $T$, then for every sufficiently large numerator scale $V$, then for every sufficiently large prime endpoint $X$. This order permits passage to the explicitly evaluated series. For fixed $T,V$, the prime number theorem in arithmetic progressions identifies the prime average with the uniform mean over the units modulo $T!$. In the twisted mean the only surviving denominators are odd multiples of three. [Ordered approximation](ThetaPrimeTailTransfer.lean) · [Finite unit means](ThetaConditionalRows.lean)

The unsifted odd numerator sum groups into six-term blocks, with paired terms $1/(6k+1)-1/(6k+5)$. The cotangent partial fractions at $1/6$ give their sum $b=\pi/(2\sqrt3)$. An incomplete last block contributes at most $1/(6\lfloor N/6\rfloor+1)$ in absolute value. Removing the multiples of a prime $\ell$ introduces $1-\chi_3(\ell)/\ell$. The other factor, $1-\chi_3(\ell)$, comes from the character transform of the denominator row. [Cotangent evaluation](ThetaCharacterNumerator.lean) · [Sifted transform](ThetaCharacterThree.lean)

The common-factor weight tends to $\pi^2/8$, canceling the $8/\pi^2$ that converts the off-diagonal back to the canonical residual. For each odd $d$ divisible by three the resulting term is
\[
 \frac{2b}{d\varphi(d)}
 \prod_{\substack{\ell\mid d\\\ell\ {\rm prime},\ \ell\ne3}}
     (1-\chi_3(\ell))(1-\chi_3(\ell)/\ell).
\]
Summing the positive powers of three contributes $3/16$ before the common factor $2b$. Primes congruent to one modulo three annihilate the term. A prime $\ell\equiv5\bmod6$ contributes the local series $1+2/(\ell-1)^2$. The two multiplicative functions that retain or delete the prime three have absolute values bounded by $n^{-5/4}$ for positive $n$. Their absolutely convergent Euler products therefore evaluate the denominator sum. [Euler factors and absolute convergence](ThetaCharacterEuler.lean) · [Passage to the original sum](ThetaCharacterCoefficient.lean)

The paper's Section 5 treats a divisor sum associated with $T(k)$. Lägeler studies distributions of individual Hardy sums. The cited pointwise reductions of $S(k)$ and harmonic subproblem have different conclusions from the prime-average formula above. [Paper](https://arxiv.org/pdf/2501.03234v3) · [Lägeler](https://arxiv.org/abs/2207.04828) · [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/21388) · [LTS-listed harmonic step](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7126)

## Joint Lean replay

The notebook transfers take the proposition `ProgressionMangoldt` as their hypothesis. The following joint module discharges it using the existing pinned proof. [Progression theorem, pins and replay setup](NATURAL-PRIME-MEAN.md#joint-lean-replay) · [External Lean source](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/55270df807213fc3584523d09e0311d7dc073ff5/PrimeNumberTheoremAnd/Wiener.lean#L4025-L4051)

```lean
import ThetaCharacterCoefficient
import ThetaPNTCorollaries

/-! Exact character means of the pinned theta sum over the two prime classes modulo three. -/
namespace Arxiv.«2501.03234».ThetaExactCharacterPNT
open Filter ThetaCharacterCoefficient ThetaCharacterPrimeMeans ThetaNaturalPrimeMeans
open ThetaCharacterThree ThetaDiagonalConstant ThetaPNTCorollaries
open scoped Topology

theorem twisted_mean :
    Tendsto (primeMean (fun p => (chi p:ℝ)*residual p)) atTop (𝓝 characterConstant) :=
  prime_character_exact progression_mangoldt

theorem class_statistics :
    ∃ V : ℝ, characterConstant^2 ≤ V ∧
      Tendsto (classMean 1 residual) atTop (𝓝 (diagonalConstant+characterConstant)) ∧
      Tendsto (classMean 2 residual) atTop (𝓝 (diagonalConstant-characterConstant)) ∧
      Tendsto (sampleVariance residual) atTop (𝓝 V) :=
  prime_class_statistics_exact progression_mangoldt

#print axioms twisted_mean
#print axioms class_statistics
end Arxiv.«2501.03234».ThetaExactCharacterPNT
```

After building the preceding joint module, use the same bridge directory and pinned paths.

```sh
awk '/^```lean$/ { lean = 1; next } lean && /^```$/ { exit } lean { print }' \
  "$NOTEBOOK/research/arxiv/theta-sum/EXACT-MOD-THREE-BIAS.md" > "$bridge_dir/ThetaExactCharacterPNT.lean"
lake env sh -ec '
  export LEAN_PATH="$1:$2:$3:$LEAN_PATH"
  cd "$1"
  lean -o ThetaExactCharacterPNT.olean ThetaExactCharacterPNT.lean
  leanchecker -v ThetaExactCharacterPNT
' sh "$bridge_dir" "$THETA_OLEANS" "$pnt_path"
```

Both unconditional declarations report only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the derivation and formalization.
