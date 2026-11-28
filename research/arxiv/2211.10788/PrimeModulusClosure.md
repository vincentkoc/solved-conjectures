# Prime moduli detect the Lucas–Fibonacci congruence closure

For the upper sequence U(n) = Fₙ + Lₙ₊₁ and any natural candidate y, the following conditions are equivalent.

1. For every prime p, some n ≥ 0 satisfies U(n) ≡ y modulo p.
2. The same holds for every positive integer modulus.
3. The candidate occurs as U(n) or as Fₖ + Lₖ₋₁ at a positive odd index k.

The earlier proof used a composite modulus built from the squares of two discriminants. The new implication goes from prime moduli alone to all moduli. The individual prime tests can use different indices. The primes 3 and 31 still pass them all without occurring on U. The pinned question asks about infinitely many primes that actually occur on U and remains open. [Prime-modulus theorem](LucasFibonacciPrimeModulusClosure.lean) · [All-moduli classification and examples](UpperCongruenceClosure.md) · [Pinned predicate](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Ching et al.](https://arxiv.org/abs/2211.10788)

## A progression of detecting primes

If y lies on neither diagonal, set A = 5y² + 44 and B = |5y² − 44|. Let M be eight times the product of the distinct odd primes dividing AB. There is a reduced class r modulo M such that **every prime p in the class excludes y at every index**. For example, at y = 6 one can take r = 477 modulo 952. Here A = 224 = 2⁵·7 and B = 136 = 2³·17. The class makes 2 a nonsquare and both 7 and 17 squares. The progression theorem also covers y = 0; one class is 57 modulo 88. [Obstruction theorem](LucasFibonacciPrimeModulusClosure.lean)

The pooled Pell criterion gives an integer square 5U(n)² ± 44. For a candidate outside the two diagonals, A and B are both nonsquares. For y ≥ 3 this follows directly from that criterion. Below 3 the absolute value in B gives 44, 39 or 24. A prime making A and B nonsquares and satisfying p ≡ 1 modulo 4 rules out both Pell branches, since −1 is a square there. Within the pooled range a hit modulo 11 distinguishes the upper or odd-lower orientation. The progression conclusion above is proved for candidates outside both diagonals. [Pooled Pell criterion](DiagonalUnion.md) · [Orientation at eleven](LucasFibonacciCongruenceClosure.lean)

## Prescribing the two signs

For positive nonsquares A and B, record the primes appearing to odd exponent in each. If those two sets intersect, choose a common prime. Otherwise choose one from each set. Give the chosen primes Legendre sign −1 and every other prime divisor sign +1. Then the products for A and B both have sign −1.

Quadratic reciprocity realizes this choice in one reduced class. For each odd prime divisor q use a nonzero residue of the required sign modulo q. At 2 choose 5 modulo 8 for the negative sign and 1 modulo 8 for the positive sign. The Chinese remainder theorem combines these conditions and Dirichlet’s theorem supplies arbitrarily large primes. The auxiliary Lean theorem allows an arbitrary finite collection of prime bases and arbitrary prescribed signs. Wright proves general criteria for patterns of residues and nonresidues of integers. [Lean character argument](HosoyaSimultaneousNonresidues.lean) · [Wright, Patterns of quadratic residues and nonresidues for infinitely many primes](https://www.sciencedirect.com/science/article/pii/S0022314X06001338)

Lean 4.33.1 rebuilt and independently kernel-replayed five notebook modules. All 19 named axiom reports used only `propext`, `Classical.choice` and `Quot.sound`. A separate calculation exhausted the complete U orbits at all 303 primes through 2,000. Their intersection on 0 ≤ y ≤ 10,000 matched the stated range. All 16 sign prescriptions on 2, 3, 5 and 7 also agreed with direct modular exponentiation at the 57 prime representatives through 5,000 in the chosen classes. [Notebook replay](../../README.md#replay)
