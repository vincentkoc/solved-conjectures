# Power classes and rational power relations in Hosoya windows

Fix a finite set of primes `S` and a radius `H`. Sample the possible starts of a forward window in **any** interval of `N` consecutive indices. Except for a proportion tending to zero, every rational product of upper and lower diagonal values in that window is a kth power times a rational S-unit **if and only if k divides every signed exponent in the product**. This holds simultaneously for all positive integers k up to a cutoff growing as a positive power of N. The starting interval can move arbitrarily with N. No superelliptic estimate is assumed. The previous conditional theorem gives the criterion at every sufficiently late start for all exponents. [Density theorem](HosoyaWindowPowerDensity.lean) · [Rational power criterion](HosoyaDetectedPowerRelations.lean) · [Earlier theorem and external hypotheses](PowerRelationsInWindows.md)

At counter `i` the two values are the upstream upper sequence `U(i+2) = 2Fᵢ₊₂ + Fᵢ₊₄` and the lower neighbor `2Fᵢ₊₂ + Fᵢ`. The window includes both sides at every counter from `n` through `n+H`. A rational S-unit has numerator and denominator supported on S and can have either sign. Infinitude of primes equal to an upper value remains open. [Pinned upper sequence and conjecture](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Diagonal definitions](LucasFibonacciToralGaps.lean) · [Ching et al.](https://arxiv.org/abs/2211.10788)

## Separation in one power class

For either diagonal, let `f(i) = d yᵏ` and `f(j) = d zᵏ`, with `i < j`, `k ≥ 2`, and `j − i` divisible by `2k`. Then

$$
 f(j)\le 11 F_{j-i}^{\,2},\qquad j\le 4(j-i)+8.
$$

Both bounds are uniform in the multiplier d and the exponent k. Consequently any interval of `16·2ʳ` consecutive indices contains at most `16 + 32kr` terms of the form `d yᵏ` on either specified diagonal. The earlier dyadic square-class theorem has a better constant for squares. The argument here also works for every odd exponent. [Power-class spacing and count](HosoyaPowerClassIntervals.lean) · [Earlier square-class bound](SquareClassWindows.md)

Write `j − i = hk`, where h is positive and even. For the golden ratio φ and its conjugate ψ, the product `(z−φʰy)(z−ψʰy)` is a nonzero integer. Its integrality follows from the Lucas trace and the norm of φ. Its nonvanishing follows from the Fibonacci expression for φʰ and ψʰ and their irrationality for positive h. Both real conjugates raised to the even power h are positive. For nonnegative $x$ and $a$, the inequality $|x^k-a^k| \ge x^{k-1}|x-a|$ holds. Applying the inequality on both sides shows that the absolute norm of the kth-power differences is at least $z^{2k-2}$. After multiplication by `d²`, this is at least `f(j)`. Cassini’s identity computes the same scaled norm as `11 F²_{j−i}`. [Integer norm](HosoyaConjugatePowerNorm.lean) · [Recurrence identity](HosoyaRecurrenceGapNorm.lean) · [Comparison for two terms](HosoyaRepeatedClassBound.lean)

## Exceptional windows

Let E consist of S together with the prime divisors of the product of the shift determinants through radius H, and put `b = |E|`. A divisor outside E cannot occur at two distinct sites within distance H. If every prime outside E occurs in a term to multiplicity divisible by k, its residual power class is determined by the `b` exponents modulo k. There are at most `kᵇ` possible classes. Applying the spacing bound, and then taking the union over all sites and moduli, gives at most

$$
2(H+1)K^{b+1}(16+32Kr)
$$

exceptional starts in any interval of `16·2ʳ` starts, for all moduli from 2 through K. At a remaining start, take a valuation at a prime unique to the site. If k fails to divide a signed site exponent e, put `t = k/gcd(k,|e|)`. Some exclusive prime has multiplicity indivisible by t. Its valuation prevents the product from being an S-unit times a kth power. [Power-class representatives](HosoyaPowerClassFactors.lean) · [Window count](HosoyaDetectedPowerWindows.lean) · [Valuation argument](HosoyaDetectedPowerRelations.lean)

For arbitrary positive N, set `r = ⌊log₄ N⌋` and `K = 2^⌊r/(b+2)⌋`. The count of exceptions is at most `160(H+1)(r+1)2ʳ`, uniformly in the initial index. Since `4ʳ ≤ N`, the exceptional fraction tends to zero. For example, taking one site and one exponent equal to one excludes every kth power times an S-unit there, simultaneously for `2 ≤ k ≤ K`. Effective finiteness results for fixed twists of nondegenerate binary recurrences are classical. The estimate here counts terms uniformly over all multipliers, and the window criterion permits rational products with varying signed exponents. [Explicit count and limit](HosoyaWindowPowerDensity.lean) · [Bennett on perfect powers in recurrence sequences](https://personal.math.ubc.ca/~bennett/Be-PellPower.pdf) · [Bérczes et al. on superelliptic equations](https://arxiv.org/abs/2310.09704)

Independent integer checks verified 4,320 power-norm inequalities and 3,840 gap identities on the two diagonals. DeepMind and Open Math Agents searches for the arXiv number, Hosoya power classes, perfect powers and gap principles returned the upstream statement formalization. No corresponding entry appeared among 12,841 Left to Solve DeepMind records. These checks concern formalization overlap. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/8156) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents) · [Left to Solve](https://lefttosolve.com/api/solved?source=deepmind)

A fresh Lean 4.33.1 build and independent kernel replay checked 17 notebook modules. All 58 named axiom reports used only `propext`, `Classical.choice` and `Quot.sound`. The 11 named theorems in the eight new modules each have an axiom report. Run the focused notebook replay with `HosoyaWindowPowerDensity`. [Replay instructions](../../README.md#replay)
