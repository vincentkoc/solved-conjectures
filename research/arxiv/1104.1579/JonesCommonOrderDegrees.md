# Multiplicative orders and Jones polynomial degrees

For Jones’s fourth parameter, put `Pⱼ = 342 + X + ⋯ + Xʲ`. For every prime q < 100,000 other than 3, **P at degree qⁿ is irreducible over ℚ for every n ≥ 0**. All prime degrees below 100,000 are irreducible, including 3. At degree 9 the polynomial has root −2. A separate infinite family has degrees `59ᵃ·233ᵇ` with unrestricted natural a and b. [Prime-power and mixed-degree theorems](CunninghamJonesFourthPrimePowers.lean) · [Earlier Frobenius criterion](JonesFrobeniusDegrees.md)

Jones’s Conjecture 4.1 gives constant 342 at k = 6 and 7 and predicts degree 9 as the unique reducible case in its range. Other composite degrees remain open at this parameter. The pinned DeepMind predicates require a natural seed, k initial prime terms under one of the two integer recurrences, and a nonprime term at index k. The infinitude questions for those predicates remain open. [Jones, p. 7](https://arxiv.org/pdf/1104.1579#page=7) · [Pinned chain declarations](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean)

## How factor degrees rule out a split

Let m ≥ 2, j > 0 and gcd(m,j) = 1. Suppose k divides the multiplicative order of p modulo q for every pair of primes p dividing m and q dividing j. **If k does not divide j, then `m + X + ⋯ + Xʲ` is irreducible over ℚ.** In particular, for a safe prime q = 2ℓ + 1 with ℓ prime, all degrees qⁿ work provided every prime p dividing m satisfies p < q−1. Indeed p² differs from 1 modulo q, so ℓ divides its order. [General criterion and safe-prime theorem](CunninghamJonesCommonOrder.lean)

In a nontrivial monic integral factorization AB, both constants have absolute value greater than one. Choose a prime p dividing B(0). Modulo p, B is divisible by X, leaving A as a divisor of `1 + X + ⋯ + Xʲ⁻¹`. This sum takes the nonzero value j at 1. For any irreducible factor of A of degree e, a root has multiplicative order d > 1 dividing j. The root belongs to a field of size pᵉ, so d divides pᵉ−1. For any prime q dividing d, the order of p modulo q divides e. Summing the degrees shows k divides deg A. Using a prime of A(0) in the same argument shows k divides deg B, hence k divides j. [Finite-field degree lemma](CunninghamJonesOrderDegrees.lean) · [Factor constant bound](JonesLargeDegree.md)

At q = 59 the orders of 2, 3 and 19 are 58, 29 and 29. At q = 233 they are 29, 232 and 29. The common divisor 29 excludes a split at every degree `59ᵃ·233ᵇ`.

## Certifying the prime bases

A reducible fourth-parameter degree j must satisfy j ≡ 9 modulo 90 or j ≡ −1 modulo 30. At j = qⁿ, the first alternative forces q = 3. In the second, q itself must be −1 modulo 30. Every residue x modulo 30 satisfies x⁵ = x, and checking the first four positive powers shows only −1 can reach −1. [Complementary congruences](JonesComplementaryOrders.md) · [Prime-base reduction and finite certificate](CunninghamJonesFourthPrimePowers.lean)

There are 1,198 prime bases below 100,000 in this remaining class. For each, Lean verifies a prime ℓ and b ∈ {1,2} such that ℓᵇ divides q−1 and none of 2, 3 and 19 raised to `(q−1)/ℓᵇ` equals 1 modulo q. Thus ℓ divides all three orders and cannot divide qⁿ. At q = 31,769 the test needs b = 2 and works with ℓ = 19. The finite computation bounds the prime base alone.

An independent calculation checked every one of the 1,198 certificates by modular exponentiation and counted the 70 positive-degree divisors away from 1 in 18,516 small monic polynomial cases over the fields of sizes 2, 3 and 5. Lean 4.33.1 rebuilt and independently kernel-replayed eight notebook modules. Their 34 named axiom reports use only standard axioms from `propext`, `Classical.choice` and `Quot.sound`. [Notebook replay](../../README.md#replay)
