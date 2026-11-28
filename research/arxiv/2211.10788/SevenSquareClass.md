# Seven times a square on the neighboring Hosoya diagonals

Let `Uₙ = Fₙ + Lₙ₊₁` and `Vₙ = Fₙ + Lₙ₋₁`. No upper value is seven times a square. On the lower diagonal, the complete list is `V₄ = 7·1²` and `V₁₂ = 7·7² = 343`. The lower sequence starts at physical index one with value 3, and the Lean function `lowerNeighborAtAddTwo m` gives the value at `n = m+2`. [Square-class proof](HosoyaSevenSquareClass.lean) · [Ching et al., neighboring prime values](https://arxiv.org/abs/2211.10788)

A prime is private to one neighbor when it divides that value and does not divide the other value at the same index. The only possible common prime is 7. A lower value above one lacking a private prime must therefore be a power of 7. For an even exponent this is a square, and the only lower square from index two onward is 81. For an odd exponent it is seven times a square, giving precisely the two values above. At index one the lower value 3 has its own prime divisor. This proves the exact private-prime exceptions without the three Mordell-table assumptions in the earlier proof. Those assumptions concerned the lower neighbor. The separate proper-power result for the product retains its stated inputs. [Unconditional declarations](HosoyaSevenUnconditional.lean) · [Earlier hypotheses](PowersAndPrivatePrimeDivisors.md) · [Square values](SquareValues.md)

| Consequence | Complete list |
| --- | --- |
| Powers of 7 on either diagonal, including exponent zero | 1, 7, 343 |
| Nonnegative solutions of `x² = 245y⁴ + 44` | `(x,y) = (17,1), (767,7)` |
| Nonnegative solutions of `x² + 44 = 245y⁴` | None |

The quartics follow by substituting `7y²` in the Pell criterion for the union of the two diagonals. The minus sign is impossible modulo 7. [Pell criterion](DiagonalUnion.md) · [Quartic proof](HosoyaSevenUnconditional.lean)

## Why the two lower values exhaust the class

Modulo 21 the upper recurrence has period dividing 16 and omits 0 and 7, the only residues of seven times a square. Modulo 7 the same period leaves just the physical lower index classes 4 and 12. At the first positive representative of each class, the square root after removing the factor 7 is 1 or 7.

Every later index in the same class differs by `4·2ʳ·t` with `r ≥ 2` and `t` odd. At that dyadic scale a prime `p ≡ 3 mod 4` reverses the sign of any Fibonacci recurrence modulo `p`. It cannot be 7. The shift `4·2ʳ` is a multiple of 16, and so would preserve the nonzero lower value 2 modulo 7 while also reversing its sign. Consequently both 7 and the square root at the starting index are invertible modulo `p`. A later value `7y²` would give `y² ≡ −1²` or `y² ≡ −7² mod p`, contradicting the quadratic nonresidue of −1. [Dyadic sign lemma](LucasFibonacciSquareValues.lean) · [Cohn’s dyadic congruence method](https://msp.org/pjm/1968/26-2/pjm-v26-n2-p03-p.pdf)

The pinned DeepMind proposition asks whether infinitely many distinct primes are upper values. A prime divisor produced here can be a proper divisor. The prime-values and simultaneous prime-values questions remain open. The formalization is unconditional. The six new axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`. Codex assisted with the proof. [Pinned statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/8156) · [Left to Solve](https://lefttosolve.com/api/solved) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents) · [Notebook replay](../../README.md#replay)
