# Mean-square error of the theta sum at primes

Write `E(p) = S(p)/p − (log p)/2` for the error in the original signed integer theta sum. There is an absolute constant `C > 0` such that for every integer `X ≥ 2`,

```text
Σ_{p ≤ X, p prime} E(p)² ≤ C X.
```

Thus at most `C X/t²` primes up to `X` have `|E(p)| ≥ t`, simultaneously for every real `t > 0`. The constant is existential. The square sum controls the sizes of the exceptional values left by the earlier density theorem. [Finite moment and threshold count](ThetaPrimeMeanSquare.lean) · [Previous density bound](PRIME-ASYMPTOTIC.md)

For the relative error `e(p) = S(p)/(p log p) − 1/2`, the same argument gives an absolute `C′ > 0` with

```text
Σ_{p ≤ X} e(p)² ≤ C′ X/(log X)²                              (X ≥ 4),
(1/π(X)) Σ_{p ≤ X} e(p)² ≤ C″/log X                         (eventually),
(1/π(X)) Σ_{p ≤ X} |e(p)| ≤ C‴/sqrt(log X)                   (eventually).
```

All three sums range over primes. In particular, if `η(X) > 0` and `η(X)² log X → ∞`, the fraction of primes `p ≤ X` with `|e(p)| ≥ η(X)` tends to zero, by the squared-mean inequality. This shrinking-tolerance consequence follows from `prime_mean_relative_square`; the three displayed bounds each have their own Lean declaration. [Relative bounds](ThetaPrimeMeanSquare.lean)

## Cancellation independent of window width

For a reduced Fourier denominator `q`, write the original modulus as `d = qm`. The projected vector `V(w)` of an odd coprime numerator has Euclidean norm at most `τ(m)/m`; other numerators give the zero vector. The divisible row `d = 1` already belongs to the deterministic main term. For `d > 1`, the vectors have period `2d`, and `V(2d−w) = −V(w)` for `0 ≤ w ≤ 2d`. On the odd support, negation replaces a nonzero least residue `a` by `d−a`, reversing its parity. Each complete period therefore has vector sum zero, and every prefix has norm at most `2d τ(m)/m`. [Period, reflection and prefix bound](ThetaUniformWindows.lean)

Up to `2d` the reciprocal weights sum to at most `2H_d`. After that first period, summation by parts bounds the entire weighted tail by `τ(m)/m`, however far the window extends. The resulting row bound `3 H_d τ(m)/m` is independent of its width. This gives a single primitive Fourier-energy bound for all windows omitting `d=1`. The three-band large sieve then gives the same second-moment constant for a different window at every scale. [Uniform row and energy estimates](ThetaUniformWindows.lean) · [Large-sieve transfer](ThetaReciprocalVariance.lean)

## Return to the integer sum

For `N^56 ≤ p ≤ N^64`, choose the largest odd width `K ≤ N`. The cone approximation contributes an error at most `2300000 p + (2p/K)(1+log p)`. Because `K ≥ N/2` and `log p ≤ 64 log N`, this is `O(p)` uniformly. After removing the diagonal `(p/2) log p + O(p)`, the error `|E(p)|` is bounded by a constant plus an absolute multiple of the interpolating Fourier sum. Squaring, summing over the primes in the band, and applying the uniform variance on all integers gives `O(N^64)`. Below `N^56`, the pointwise Fourier bound gives `O(N^60)` for the sum of squares. Interpolating between consecutive 64th powers yields the assertion for every endpoint. [Diagonal](DIVISIBLE-DIAGONAL.md) · [Cone approximation](ThetaPrimeAsymptotic.lean) · [Global Fourier bound](FOURIER.md) · [Prime transfer](ThetaPrimeMeanSquare.lean)

To pass to the relative error, split at `⌊√X⌋`. Above the split `log X ≤ 2 log p`; below it use the finite moment up to `⌊√X⌋`, `log p ≥ log 2`, and `⌊√X⌋ (log X)² ≤ 16X`. Chebyshev’s lower bound on `π(X)` supplies the prime denominator. Cauchy–Schwarz gives the absolute mean. [Formal estimates](ThetaPrimeMeanSquare.lean)

## Scope and sources

Theorems above use the pinned DeepMind definition of `S`. Its Conjecture 1.1 asks for positivity at every odd prime, and Conjecture 4.4 asks for every natural linear threshold eventually at all odd primes. These pointwise lower bounds, including the corresponding lower inequality in v3 Conjecture 3.3, remain open. Berndt, Bhat, Meyer, Xie and Zaharescu’s asymptotic in §5 concerns the companion sum. Lägeler studies phases of individual Hardy sums, and Liu and Zhang study moments over numerators. The checked DeepMind issue, OMA reductions and LTS entries yielded no matching prime second moment for the signed double sum in the 2026-11-28 search. [Pinned declarations](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean#L36-L95) · [Paper, §3](https://arxiv.org/pdf/2501.03234v3#page=4) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5611) · [LTS-listed lemma](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7126) · [Lägeler](https://arxiv.org/abs/2207.04828) · [Liu and Zhang](https://ir.library.osaka-u.ac.jp/repo/ouka/all/10379/1658ojm.pdf)

The scoped replay uses Lean 4.33.1, the pinned canonical source and sixteen local modules. The fifteen new or newly exposed public results report only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the derivation and formalization. [Notebook replay command](../../README.md)
