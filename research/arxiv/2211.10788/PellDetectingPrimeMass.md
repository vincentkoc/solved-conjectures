# One quarter of prime mass detects a missing Pell value

Let U(n) = Fₙ + Lₙ₊₁ and let V(k) = Fₖ + Lₖ₋₁ for k ≥ 1. For a natural candidate y outside the ranges of both sequences, exactly **one quarter** of the normalized logarithmic prime mass consists of primes p at which **both** 5y² + 44 and 5y² − 44 are quadratic nonresidues. Every such p excludes U(n) ≡ y at every index. For y on either diagonal, the set of these primes is empty. The earlier result supplied one reduced progression of excluding primes for each y. [Prime-mass theorem](LucasFibonacciPellPrimeMass.lean) · [Earlier prime-modulus theorem](PrimeModulusClosure.md)

For a set P of primes the limit proved here is

```text
lim (s − 1) ∑_{p ∈ P} log(p) / pˢ = 1/4,   s → 1 from above.
```

The set of *all* prime moduli missing y can be larger. Its normalized mass is eventually greater than each fixed c < 1/4. The canonical question asks whether infinitely many distinct primes occur as U(n). The density here is over testing moduli for a fixed y. Prime-value infinitude remains open. [Pinned DeepMind statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Ching et al.](https://arxiv.org/abs/2211.10788)

## The two quadratic characters

The pooled Pell criterion says that y occurs on one of the diagonals exactly when A = 5y² + 44 or B = 5y² − 44 is an integer square. Their product is 25y⁴ − 1936. For y ≥ 14 it lies strictly between (5y² − 1)² and (5y²)². Of the smaller candidates, only y = 5 gives a square product, and both factors at five are squares. Hence A, B and AB are all nonsquares off the two diagonals. Keeping the sign of B also covers y = 0, where A and B have the same absolute value. [Pell range criterion](DiagonalUnion.md) · [Square-product classification](LucasFibonacciPellPrimeMass.lean)

Take M = 4·|A|·|B|. The Jacobi symbols of A and B on the units modulo M are multiplicative signs. Each of the three nonsquares A, B and AB has a prime representative with symbol −1. Multiplication by that representative permutes the units, so its character sums to zero. Summing (1 − χA)(1 − χB) gives φ(M) and counts every simultaneous minus sign four times. Primes dividing M cannot give the simultaneous obstruction. The logarithmic prime mass of each reduced residue class is 1/φ(M). This is the usual quadratic-character count applied to these signed discriminants. [Character proof](HosoyaQuadraticCharacterPairs.lean) · [Prime mass of a finite union](HosoyaReducedClassMass.lean) · [Wright on quadratic residue patterns](https://www.sciencedirect.com/science/article/pii/S0022314X06001338)

At y = 6 the characters reduce to the square classes of 14 and 34. A separate enumeration counted 96 simultaneous minus classes among the 384 units modulo 952. Direct computation also checked the four sign counts at y = 0, 8, 10, 18 and 22, and found y = 5 as the only square product through 1,000,000. Across the 303 primes through 2,000 and 0 ≤ y ≤ 200, complete recurrence orbits missed 24,597 prime–candidate pairs. Of those, the two nonresidues certified 14,134. Lean 4.33.1 independently replayed seven notebook modules, with all 23 named axiom reports confined to `propext`, `Classical.choice` and `Quot.sound`. [Lean declarations and axiom reports](LucasFibonacciPellPrimeMass.lean) · [Kernel replay instructions](../../README.md#replay)
