# All-index Jones plus chains at prime-power coefficients

Let T₀ = a(X−1) and Tₙ₊₁ = XTₙ+1. For a prime p and an integer e ≥ 0 with a = pᵉ ≥ 28, every Tₙ is irreducible over ℚ if **e is odd, p = 2, or p ≡ 3 (mod 4)**. This includes the square coefficients 49, 64, 81 and 121. The previous all-index result required an odd exponent and coefficient at least 615. The threshold 28 here is sufficient. [All-index theorem](CunninghamInertPrimePowerChains.lean) · [Earlier two-sign theorem](InfiniteCommonLinearSeeds.md)

Jones’s polynomial chains use the recurrence XT ± 1 and irreducibility over ℚ. The pinned DeepMind questions instead ask, for each positive k and each sign, for infinitely many natural seeds whose first k terms under t ↦ 2t ± 1 are prime and whose next term is nonprime. Both integer questions remain open. The earlier eventual result for all balanced coefficients allows exceptional early indices. [Jones, §4](https://arxiv.org/pdf/1104.1579) · [Pinned questions and predicates](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean) · [Eventual theorem](AllBalancedEventual.md)

## What three coefficients determine

At every positive index the top three coefficients are a, −a, 1. Reverse an integral factorization and call the factors A and B. Suppose a = p²ʳ and neither constant is a unit. The constant product is a, it divides the linear coefficient, and the quadratic coefficient survives modulo p. The earlier divisibility argument then forces equal absolute constants. Their product is positive, so A₀ = B₀ = s with |s| = pʳ. The linear coefficient gives A₁+B₁ = −s. The quadratic coefficient gives A₁B₁ ≡ 1 (mod s). Hence A₁² ≡ −1 (mod pʳ). For a minus iterate the same calculation requires a square root of +1. [Constant comparison](CunninghamOddPowerFactorCriterion.lean) · [Reversed coefficients](CunninghamSharedPrimePowerPrefixes.lean) · [Both-sign obstruction](CunninghamInertPrimePowerChains.lean)

The obstruction is exact for these three coefficients. For q = pʳ and u²+ε = qv, the factors q+uX and q−(q+u)X+(v+u)X² have product coefficients q², −q², ε in degrees zero through two. For ε = 1 the congruence is solvable precisely when p ≡ 1 (mod 4), or p = 2 and r = 1. At an odd prime, once a root exists modulo p, it lifts through every power. One explicit lift sends u to u(1+c(u²+1)), where 2c = p+1. At p = 2 a square cannot be −1 modulo 4. [Construction and lift](CunninghamEvenPowerResidues.lean)

For a = bc with coprime b,c > 1, Bézout gives ub+vc = 1. The factors b−bX+vX² and c+uX² then have the required three coefficients and two nonunit constants. Combining this example with the even-power calculation and the odd-power criterion gives a converse for **every** a ≥ 28. The triple a, −a, 1 forces a unit constant in every factorization realizing it exactly for the prime powers in the theorem. These constructed products certify the limits of the coefficient test. Reducibility of an actual Jones iterate requires matching its other coefficients too. [Exact classification](CunninghamLeadingTriple.lean)

## Why the bound works for all indices

Take K with coefficients in ascending order

```text
2, 8, 21, 42, 72, 112, 160, 217, 279, 343, 405, 460, 503, 527, 527, 498, 433, 330, 186.
```

Set H = Tₙ · (X−1) · K. Its degree is n+20 and its leading coefficient is 186a. The recurrence telescopes to H = Xⁿ(a(X−1)²K+K)−K. Write E for the sum of the squared coefficients below the leading term. Expanding (186a)²−4E gives a quadratic in a whose dependence on n comes only from overlapping coefficients of K. Truncating n at 20 preserves the overlap sum. Its quadratic coefficient is 4. In all 21 rows the margin at a = 28 is at least 3,136 and its derivative there is at least 224. Thus the margin is positive for every a ≥ 28. Lean checks strict positivity at 28 and nonnegativity of the derivative in every row. [Multiplier certificate](CunninghamPlusMultiplier.lean) · [Coefficient-list representation](CunninghamFiniteMultiplier.lean) · [Telescoping identity](CunninghamBalancedEnergy.lean)

At a positive index the constant term of Tₙ is 1. The three-coefficient argument forces some factor to have unit leading coefficient as well. The strict energy inequality makes that factor reciprocal up to sign. The earlier reciprocal-root theorem excludes any nonconstant such factor. Gauss’s lemma transfers the conclusion to ℚ, and the index-zero seed is linear. [Factor argument](CunninghamInfiniteSharedLinearChains.lean) · [Reciprocal-root exclusion](CunninghamReciprocalUnitFactors.lean)

Independent integer arithmetic checked 484 energy identities and both signs at 48 prime-power levels. Independently of the multiplier, full-degree irreducible reductions over prime fields certified all 210 sampled plus iterates at 14 eligible coefficients and indices 1 through 15. The largest field used had 283 elements. Replay `CunninghamInertPrimePowerChains` for the infinite theorem and the local converse. [Replay instructions](../../README.md#replay)
