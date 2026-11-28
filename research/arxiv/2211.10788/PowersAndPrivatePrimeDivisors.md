# Perfect powers and private prime divisors of neighboring Hosoya values

Write `Uₙ = Fₙ + Lₙ₊₁` and `Vₙ = Fₙ + Lₙ₋₁`, for positive indices. Call a prime divisor of one neighbor **private** if it does not divide the other at the same index. The following conclusions use the published inputs indicated in the table. For `n ≥ 2`, the Lean lower neighbor is `lowerNeighborAtAddTwo (n−2)`. At `n=1` the values are 4 and 3, so the product is 12 and each neighbor has a private divisor. [Product proof](HosoyaNeighborProductPowers.lean) · [Prime-divisor proof](HosoyaNeighborPrimeSupport.lean)

| Conclusion | External input to Lean |
| --- | --- |
| Only 7 can divide both neighbors. The upper value always has a private prime divisor. | None |
| The lower value has a private prime divisor at every index except 4 and 12. | Three specified rows of Bennett and Ghadermarzi’s Mordell table |
| The product is never square. At odd indices it is also never a cube. | None |
| The product is never a proper power, for any integer exponent at least two. | The coefficient-11 case of Bennett–Skinner’s Theorem 1.1 and the Mordell row for 1331 |

**The two exceptions.** At index 4 the upper and lower values are 14 and 7. At index 12 they are 665 and 343. In both cases 7 divides the upper value and is the only prime divisor of the lower value. To see why only 7 can be shared, use `Uₙ+Vₙ=7Fₙ` and `Uₙ=3Fₙ+Fₙ₊₁`. Consecutive Fibonacci numbers are coprime. If the upper value had no private prime divisor, it would therefore be a positive power of 7. Every positive power of 7 equals 7 modulo 21. The upper sequence has period dividing 16 modulo 21 and omits 7 throughout that period. [Proof of the upper assertion](HosoyaNeighborPrimeSupport.lean)

For the converse on the lower side, the only powers of 7 on either diagonal, allowing exponent zero, are 1, 7 and 343. The earlier diagonal criterion gives `x² = 5·7²ᵏ ± 44`. For `k > 0` the minus sign is impossible modulo 7. For the plus sign write `k=3j+r` and set `a=7ʲ`. Scaling gives the following three integral points on `Y²=X³+C`. [Diagonal criterion](DiagonalUnion.md) · [Bennett and Ghadermarzi, *Mordell’s equation: a classical approach*](https://doi.org/10.1112/S1461157015000182)

| r | (X,Y) | C | Possible X in the complete row |
| --- | --- | --- | --- |
| 0 | (5a², 5x) | 1100 | −10, 5, 14, 245 |
| 1 | (245a², 245x) | 2641100 | 245 |
| 2 | (245a², 35x) | 53900 | −35, −10, 14, 70 |

The first row forces `j ≤ 1`, the second forces `j=0`, and the third has no admissible `X`. Direct evaluation gives the three witnesses. Strict growth of the lower diagonal from index two locates its powers of 7 uniquely. The hypothesis `HosoyaSevenMordellRows` states the three lists of possible integer X-coordinates. The computations establishing completeness are external to Lean. [Row 1100, p. 11](https://personal.math.ubc.ca/~bennett/0-10%5E6n.pdf#page=11) · [Row 53900, p. 320](https://personal.math.ubc.ca/~bennett/0-10%5E6n.pdf#page=320) · [Row 2641100, p. 1446](https://personal.math.ubc.ca/~bennett/2*10%5E6-3*10%5E6n.pdf#page=1446)

**Excluding proper powers.** The product is `11Fₙ²−(−1)ⁿ`. At even indices it is −1 modulo 11, a nonsquare. At odd indices it is 3 or 5 modulo 7, by the Fibonacci period modulo 7. Neither residue is a square or a cube. If the product at an even index were `y³`, then `(X,Y)=(11y,121Fₙ)` would solve `Y²=X³+1331`. The row lists `X=−11,37`. Neither can be a nonnegative multiple of 11. [Earlier product identity](NeighboringPrimePairs.md) · [Row 1331, p. 13](https://personal.math.ubc.ca/~bennett/0-10%5E6n.pdf#page=13)

For an odd exponent `k ≥ 5`, the equation becomes `yᵏ + (±1)ᵏ = 11Fₙ²`. The sign is fixed by the index parity. The variables are pairwise coprime because a common divisor of `y` and `Fₙ` divides 1. In the coefficient-11 case of Bennett and Skinner’s Theorem 1.1 the only ordered exception is `3⁵+2⁵=11·5²`. Its smaller base is 2, so it cannot occur here. Even exponents were already excluded by the square argument. The formal hypotheses `BennettSkinnerEleven` and `Mordell1331RowComplete` record the published statements used at this step. [Bennett and Skinner, Theorem 1.1](https://doi.org/10.4153/CJM-2004-002-2)

**Scope and verification.** Ching et al. ask whether the two known indices with both neighbors prime have a successor. DeepMind’s declaration asks for infinitely many distinct prime upper values. A private divisor can be proper, and the product of two distinct primes is already free of proper powers. Both prime questions remain open. The main declarations are `neighboring_product_ne_power`, `upper_has_private_neighbor_prime` and `lower_has_private_neighbor_prime_iff`, in namespace `Arxiv.«2211.10788»`. [Primary question, p. 3](https://arxiv.org/pdf/2211.10788#page=3) · [Pinned upper declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean)

Open and closed DeepMind and OMA issues and pull requests and LTS solved records were searched for the paper, sequence, neighboring product, private prime divisors, and the two Diophantine inputs. The closest named searches found the canonical question, a different Lebesgue–Nagell equation, and OMA reductions of Beal’s conjecture. No matching formal result appeared in these searches. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/8156) · [Lebesgue–Nagell issue](https://github.com/google-deepmind/formal-conjectures/issues/431) · [OMA Beal reduction](https://github.com/lefttosolve2/open-math-agents/pull/8621) · [LTS](https://lefttosolve.com/api/solved)

Lean 4.33.1 compiled the pinned source and four notebook modules from fresh output. Independent kernel replays passed for each module. All 17 named axiom reports used only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the formalization. [Replay instructions](../../README.md#replay)
