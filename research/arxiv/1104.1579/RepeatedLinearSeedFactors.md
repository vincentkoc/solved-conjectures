# When does a factor repeat in a polynomial Cunningham chain?

Start both Jones recurrences at the same integral linear seed aX+b, with a > 0. The first kind takes T to XT+1 and the second takes T to XT−1. Consider all **positive** indices of the two chains. Two distinct signed indices share a nonconstant rational polynomial factor exactly for the following seeds.

- b equals a−1, a or a+1.
- a−2b equals 4 or −4.
- (a,b) equals (1,−1) or (2,0).

All other seeds have pairwise coprime terms, in particular every a(X−1) with a ≥ 2. The first seven positive indices of both signs suffice to decide the property. Seven is sharp. For X−1 all terms through index six are pairwise coprime, and Φ₆ divides first-kind terms one and seven. This criterion allows an individual iterate to be reducible. [All-seed classification and sharpness](CunninghamLinearFactorDisjointness.lean) · [Jones's polynomial recurrences](https://arxiv.org/abs/1104.1579)

## The noncyclotomic collisions

Write ε for the sign of the earlier term. At positive indices m < n, roots outside the roots of unity can repeat only between opposite signs. The following four rows are necessary and sufficient. The last column gives the polynomial whose roots are shared.

| Earlier m | Later n | Earlier sign and seed condition | Shared factor |
| --- | --- | --- | --- |
| 1 | 2 | a−2b = −4ε | 2X+1 |
| 1 | 3 | ε = +1, seed 2X+1 | 2X²+X+1 |
| 2 | 3 | ε = −1, seed 2X | 2X²+2X+1 |
| 2 | 4 | ε = +1, seed 2X+2 | 2X²+1 |

For a fixed sign, a common root at distinct indices must be a root of unity. At equal positive indices, two opposite signs can only share roots of unity as well. Combining the table with the earlier cyclotomic classification gives the seed conditions above. [Noncyclotomic table](CunninghamSharedFactorTable.lean) · [Repeated roots and exceptional seeds](CunninghamRepeatedRootSeeds.lean) · [Cyclotomic classification](LinearCyclotomicFactors.md)

## Why the later index cannot exceed four

Eliminating the seed at a common noncyclotomic root z gives 2zⁿ = zⁿ⁻ᵐ+1. Put g = gcd(m,n). After division by Xᵍ−1 the resulting trinomial has an irreducible cofactor Q of degree n−g, leading coefficient 2 and constant coefficient 1. This irreducibility is the reciprocal of a case of Koley and Reddy's theorem. The Lean proof uses the fact that all roots of Q have modulus less than one. Gauss's lemma then transfers divisibility of the earlier iterate by Q to the integral polynomial ring. [Koley and Reddy, Theorem 3](https://ssmr.ro/bulletin/pdf/63-1/articol_6.pdf) · [Trinomial identity](CunninghamCollisionTrinomial.lean) · [Cofactor irreducibility](CunninghamCollisionCofactor.lean)

Reducing modulo two lowers the degree of Q by m. The earlier iterate has degree m+1, so its reduction must have degree at most one. For m ≥ 3 its quadratic coefficient is ±1, a contradiction. Thus m ≤ 2. The degree bound n−g ≤ m+1 leaves just the four index pairs in the table. Comparing coefficients in the remaining linear or constant quotient gives the seed conditions. [Reduction modulo two](CunninghamRepeatedRootIndices.lean) · [Integral divisibility and index pairs](CunninghamOppositeRootReduction.lean)

The pinned DeepMind predicates require natural prime terms under p ↦ 2p±1 and an exact nonprime stopping term. The statements here concern factors in ℚ[X]. The integer infinitude questions remain open. An independent calculation checked 30,096 opposite-sign polynomial gcds against the four rows. A second calculation checked all 47,196 pairs through index 12 on 171 seeds. Exactly 34 of those seeds had a repeat, each at or before seven. A clean Lean 4.33.1 replay checked ten modules and 27 named axiom reports within `propext`, `Classical.choice` and `Quot.sound`. [Pinned predicates](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean) · [Kernel replay instructions](../../README.md#replay)
