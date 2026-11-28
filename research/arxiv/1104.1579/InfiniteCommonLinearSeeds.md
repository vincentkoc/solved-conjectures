# Infinite polynomial Cunningham chains from one linear seed

Start both Jones recurrences at T₀ = a(X−1), and for each sign ε ∈ {+1,−1} put Tₙ₊₁ = XTₙ + ε. **If a ≥ 615 is a prime raised to an odd exponent, every Tₙ is irreducible over ℚ for both signs.** For instance, 2048(X−1) works at every index since 2048 = 2¹¹. Among all integral linear seeds aX+b with a > 0, having both chains irreducible at every index requires b = −a and a ≥ 2. The sufficient condition leaves open other coefficients on this line. [Theorems and example](CunninghamInfiniteSharedLinearChains.lean)

Jones's Corollary 1.6 proves existence of infinite polynomial chains of each kind. His concluding remarks give the linear seeds pX+1 for the plus sign and X−c for the minus sign. The result here fixes the same seed before choosing the sign. It also removes the factor-degree bound from the notebook's earlier result for these coefficients. The pinned DeepMind conjectures ask for infinitely many natural seeds at each specified positive length, with prime terms under q ↦ 2q ± 1 before the first composite. Both integer questions remain open. [Jones, Corollary 1.6 and §4](https://arxiv.org/pdf/1104.1579) · [Earlier degree-bounded theorem](BoundedDegreeChains.md) · [Pinned definitions and conjectures](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean)

## Isolating the leading coefficient

For a nonzero integer polynomial H let its tail weight be the sum of the squares of all coefficients below its leading term. Suppose four times that weight is strictly less than the square of its leading coefficient. In any factorization H = AB where A has unit leading and constant coefficients, A must agree with its reversal up to sign. To see this, replace A by its reversal with sign chosen to preserve the leading coefficient. The product with the reversal of H, and hence its middle coefficient, stays fixed. This middle coefficient is the total squared coefficient weight. Both polynomials therefore have the same tail weight. If they differed, their highest coefficient difference would be a nonzero multiple of the leading coefficient of B, whose absolute value is the absolute leading coefficient of H. At that index the square of the difference is at most twice the sum of the two squared coefficients, strictly below the leading square. [Reversal lemma](CunninghamCoefficientEnergy.lean) · [Related weight arguments of Sawin, Shusterman and Stoll](https://arxiv.org/abs/1803.10811)

Take K to be the sum of X^(64−2i)(1+X+⋯+X^(i−1))² for 1 ≤ i ≤ 32. It has degree 62 and leading coefficient 32. Its total squared coefficient weight is 3,023,024. The tail weight of P = (X−1)²K is just 96. The telescoping identity gives

```text
Tₙ (X−1) K = a Xⁿ P + ε (Xⁿ−1) K.
```

The leading coefficient on the left is 32a. Its tail weight is at most 192a² + 8·3,023,024 by applying (u±v)² ≤ 2u²+2v² twice. This is strictly less than (32a)²/4 for every a ≥ 615, including indices where the coefficient ranges overlap. The number 615 is a sufficient bound from this estimate. [Explicit multiplier](CunninghamFiniteMultiplier.lean) · [Uniform estimate](CunninghamBalancedEnergy.lean)

## Excluding the reciprocal factor

At n > 0, Tₙ has unit constant coefficient. When a is a prime raised to an odd exponent, comparison of the leading coefficients of an integral factorization forces one factor A to have unit leading coefficient. Apply the reversal lemma to Tₙ (X−1) K with the multiplier included in the other factor. If A were nonconstant, any complex root z of A and its inverse would both be roots of Tₙ and algebraic integers. Here z ≠ 0 by the unit constant coefficient and z ≠ 1 because Tₙ(1) = εn. Substitution in the reciprocal-root identity gives

```text
z + 1/z = 2a/(a+ε).
```

A rational algebraic integer is an integer. This forces a+ε to divide 2ε, impossible for a ≥ 4. Thus A is a unit. Gauss's lemma gives irreducibility over ℚ, and T₀ is linear. For the necessary condition on aX+b, if a+b ≠ 0 one sign gives a root at 1 at index |a+b|. On the remaining line the seed X−1 has a proper sixth cyclotomic factor at plus index 7. [Prime-power factor lemma](CunninghamSharedPrimePowerPrefixes.lean) · [Trace obstruction](CunninghamReciprocalUnitFactors.lean) · [Cyclotomic factors](CunninghamLinearCyclotomicFactors.lean)

Independent integer arithmetic reconstructed K from the sum and checked the strict tail inequality at 2,718 combinations of coefficient, sign and index, through index 150. Full-degree irreducible reductions modulo primes at most 197 certified all 192 terms for a ∈ {617, 1331, 2048, 2187, 3125, 16807}, both signs and indices 1 through 16. A clean Lean 4.33.1 build and independent kernel replay checked all thirteen modules. All 32 named axiom reports used only standard axioms. [Kernel replay instructions](../../README.md#replay)
