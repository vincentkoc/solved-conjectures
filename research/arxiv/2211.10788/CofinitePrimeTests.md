# Prime tests after any finite deletion

Write U(n) = Fₙ + Lₙ₊₁ and V(k) = Fₖ + Lₖ₋₁ for k ≥ 1. Delete **any finite set of primes**, including 11. A natural number y occurs in the U orbit modulo every remaining prime if and only if y is an upper value U(n) or a lower value V(k) at a positive odd index. In particular, each candidate outside these ranges is excluded at arbitrarily large primes. The old proof used a hit at 11 to distinguish the even lower values. [Cofinite prime test](LucasFibonacciCofinitePrimeTests.lean) · [Original prime-modulus classification](PrimeModulusClosure.md)

More quantitatively, let P(y) be the set of primes p for which every upper term misses y modulo p. Outside the two stated ranges, for every real c < 1/16 and every s sufficiently close to 1 from above,

```text
(s − 1) ∑_{p ∈ P(y)} log(p) / pˢ > c.
```

For candidates outside both complete diagonals, the earlier simultaneous Pell certificate already gives a lower bound of 1/4. The case that required a different argument was y = V(k) with k even. A union of reduced residue classes of exact mass 1/16 excludes every such candidate outside the upper range. Additional primes can also exclude it. The pinned question counts primes that occur as U(n), and remains open. [Quarter-mass theorem](PellDetectingPrimeMass.md) · [Canonical predicate](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Ching et al.](https://arxiv.org/abs/2211.10788)

## Separating the even indices

Choose a prime where 5 is a square and −1 and 11 are nonsquares. Let α, β be the roots of X² − X − 1, and put C = 4 − β and D = α − 4. Then αβ = −1 and CD = −11. The upper recurrence gives (α−β)U(n) = Cαⁿ + Dβⁿ. The lower recurrence gives (α−β)V(k) = −Dαᵏ − Cβᵏ for k ≥ 2. If an even upper and an even lower term coincide, set t = α^(n/2) and u = α^(k/2). Clearing the inverse powers gives

```text
(t²u² + 1)(Ct² + Du²) = 0.
```

The first factor would make −1 a square. The second would make 11 the square of Ct/u. Thus every even upper term misses the chosen even lower value. For odd n, the signed Pell identity makes 5U(n)² − 44 a square. Requiring B = 5y² − 44 to be a nonsquare excludes the odd indices as well. [Recurrence and parity proof](HosoyaEvenDiagonalSeparation.lean)

## Counting the primes

At an even lower value A = 5y² + 44 is an integer square. Away from y = 5, the product-square classification forces B to be a nonsquare when positive. For y < 3 its absolute value is one of 44, 39 and 24. Also 5 and 11 are coprime to B. In particular, 11 dividing y would force a square to be 44 modulo 121. Consequently the four quadratic characters of B, 11, −5 and −1 are independent on the units modulo 220·|B|. All four signs are negative on exactly 1/16 of the units. There −1 and −5 are both nonsquares, so 5 is a square at each prime in those classes. Summing the prime mass of the reduced classes gives the bound. [Independence and mass](HosoyaFourCharacterObstruction.lean) · [General character count](HosoyaIndependentSignClasses.lean) · [Wright on residue patterns](https://www.sciencedirect.com/science/article/pii/S0022314X06001338)

Independent enumeration found respectively 80/1280, 660/10560 and 5860/93760 qualifying classes for y = 2, 7 and 19. Complete recurrence orbits confirmed all 9,848 predicted exclusions at the first 30 even lower indices and primes through 50,000. Lean 4.33.1 independently replayed all 13 notebook modules. The 43 named axiom reports used only `propext`, `Classical.choice` and `Quot.sound`. [Kernel replay instructions](../../README.md#replay)
