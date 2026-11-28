# An exponential initial degree range for Jones polynomials

For an odd `t ≥ 3`, set `m = 2(2ᵗ+1)/3` and let `Pⱼ(X) = Xʲ + ⋯ + X + m`. Suppose that `(2ᵗ+1)/3` is prime. Then for every positive degree satisfying

```text
j³ · 2^(2(t+1)) ≤ m³,
```

**Pⱼ is reducible over ℚ exactly when j = t.** The cutoff is `⌊m / 2^(2(t+1)/3)⌋`, of order `2^(t/3)`. At `t = 43` the result covers every degree from 1 through 8,669, including every previously surviving degree `87, 131, …, 8667`. A Lucas primality certificate with base 3 verifies the odd part `2,932,031,007,403`. At the exceptional degree the polynomial has the root −2. [Lean proof](CunninghamJonesFactorTrace.lean) · [Earlier degree obstruction](JonesFactorOrders.md)

## The next coefficient of a factor

Write `M = m−1` and `N = j+1`. Every root α of Pⱼ satisfies `αᴺ = m−Mα`, by multiplying the polynomial by `X−1`. Let A be a monic integral factor of degree `e > 0`, with constant term c and coefficient a of `X^(e−1)`. When N is even, multiplication over the roots of A gives the exact integer identity

```text
cᴺ = ∏ (m−Mα) = mᵉ + a M m^(e−1) + ⋯ + c Mᵉ.
```

The right side is the value at m of A with all roots scaled by M. Modulo M² it equals `1 + M(e+a)`. For a constant-two factor with `N = k(t+1)`, the left side is `(1+3M)ᵏ`, since `2^(t+1) = 1+3M`. Canceling M gives `e+a ≡ 3k mod M`. This congruence holds for every odd Jones parameter under the stated factor hypotheses, including parameters with composite odd part.

## Why the congruence rules out factors

Assume `j < m`. At a root α the triangle inequality gives `m ≤ Σᵢ |α|ⁱ` for `1 ≤ i ≤ j`. Therefore `|α| > 1` and `m ≤ j |α|ʲ`. For a factor A with constant 2, the root norms have product 2. Multiplication gives `mᵉ ≤ jᵉ 2ʲ`. When `e ≥ 2`, expanding the product of `1+(|α|−1)` gives `Σ |α| < e+1`. Since a is minus the sum of the roots and is integral, `|a| ≤ e`. For `e = 1`, a is the constant 2.

If `k ≥ 2` and `3k < M`, these estimates and the congruence force `3k ≤ 2e`. Indeed `e+a` is nonnegative and congruent to `3k`. At degree one it equals 3, which is too small. At higher degrees it is at most `2e`. Under the displayed cutoff, cubing the root bound yields

```text
j^(3e) · 2^(2(t+1)e) ≤ m^(3e) ≤ j^(3e) · 2^(3j).
```

This would give `2(t+1)e ≤ 3j`. But `2e ≥ 3k` gives `2(t+1)e ≥ 3(j+1)`.

When the odd part of m is prime, every nontrivial rational factorization supplies a monic integral factor with constant 2. The earlier degree obstruction gives `t+1 ∣ j+1`. The cutoff implies `4j ≤ m`, so for `k ≥ 2` the hypotheses `j < m` and `3k < M` hold. Only `k = 1` survives. [Constant terms and orders](JonesFactorOrders.md) · [Rational root classification](JonesReducibilityRange.md)

## Scope and replay

Jones’s Conjecture 4.1 prescribes `t = 2⌈(k+1)/2⌉+1` and asks for the classification in every degree `j ≥ t−k`. The theorem above proves an initial range under the prime odd-part hypothesis. Higher surviving degrees and other parameters remain open in general. Large-gap theorems give eventual irreducibility at each fixed m. The two pinned DeepMind declarations ask about infinitude of prime integer seeds for exact chain lengths and remain open. [Jones, p. 7](https://arxiv.org/pdf/1104.1579#page=7) · [Sawin, Shusterman and Stoll](https://arxiv.org/abs/1803.10811) · [Pinned Cunningham declarations](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean)

Lean 4.33.1 compiled the pinned source and the four notebook modules from fresh output. Separate kernel replays passed for all four. All 17 axiom reports use only `propext`, `Classical.choice` and `Quot.sound`. The five new declarations are `jones_scaled_factor_value`, `jones_factor_trace_congruence`, `jones_constant_two_degree_bounds`, `jones_exponential_degree_range` and `jones_forty_three_degree_range`. [Notebook replay](../../README.md#replay)
