# Self-dividing upper Hosoya indices with one unrestricted prime

Let Uₙ = Fₙ + Lₙ₊₁ = 3Fₙ+Fₙ₊₁. **If n has at most one distinct prime factor outside {2,3}, then n divides Uₙ exactly when n is 1, 3 or 27.** The unrestricted prime and all exponents may be arbitrarily large. More generally, for every finite set S, all self-dividing indices with at most one prime outside S divide one explicit positive integer depending on S. Any other self-dividing index therefore has at least two distinct prime factors greater than 3. [Classification](LucasFibonacciOneOutsideIndices.lean) · [General bound and finiteness](HosoyaCofactorSupport.lean)

The pinned DeepMind question asks whether infinitely many distinct primes occur as Uₙ. Self-divisibility detects a family of witnesses to compositeness whenever 1 < n < Uₙ. The unrestricted self-divisor list and prime-value infinitude both remain open. An earlier notebook result handled prime-power indices and a completely fixed prime support. Mastrostefano and Sanna study densities for gcds of polynomial and recurrence values. Moree and Stevenhagen study primes dividing some term of this particular recurrence. [Pinned question](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Ching et al.](https://arxiv.org/abs/2211.10788) · [Earlier local theorem](IndexCommonDivisors.md) · [Mastrostefano and Sanna](https://doi.org/10.1017/S0004972718000606) · [Moree and Stevenhagen](https://arxiv.org/abs/math/9912253)

## An exact test at the cofactor

For any prime p and e,m ≥ 0, Frobenius gives U_{mpᵉ} ≡ Uₘ + (U_{pᵉ}−4)Fₘ modulo p. At odd p put χ = 5^((p−1)/2) modulo p. Then

```text
2 U_{mpᵉ} ≡ 2 Uₘ + 7(χᵉ−1) Fₘ   (mod p).
```

In the quadratic algebra with ω² = ω+1, the linear map sending x+yω to x+4y takes ωⁿ to Uₙ. The discriminant element 2ω−1 has square 5. Frobenius multiplies that element by χ, so its e-fold iterate multiplies it by χᵉ. This proves the formula even at p = 5. Away from 5 the two possible residues of U_{mpᵉ} are Uₘ and Uₘ−7Fₘ. If p divides the term at a positive cofactor m, then p divides H(m) = Uₘ(7Fₘ−Uₘ). For m ≥ 2 this is the product of the two neighboring Hosoya values. [Frobenius identities and obstruction](HosoyaPrimePowerCofactors.lean) · [Neighbor product](NeighboringLucasFibonacciPrimes.lean)

For positive n and pᵉ exactly dividing n, take m = n/pᵉ. Write rₚ for the first positive Fibonacci return modulo p, and Cₚ for the ω-coordinate of (3+ω) raised to rₚ. Then pᵉ divides Uₙ exactly when p ≠ 5, pᵉ divides Cₚ, and the displayed right side vanishes modulo p for odd p. For p = 2 the last test is n ≡ 1 modulo 3. Taking these tests over all prime factors of n decides self-divisibility. The cofactor in each odd-prime test is strictly smaller than n. [Exact local and global criteria](HosoyaLocalCofactorTest.lean) · [Prime-power lifting](HosoyaIndexCommonDivisors.lean)

## Bounding the unrestricted prime

For an index with one prime p outside S, the p-free cofactor divides B = ∏_{q∈S, q prime} Cq by the fixed-support theorem. The prime p must therefore divide H(m) for a positive divisor m of B. Adjoining the primes of these finitely many obstruction products to S bounds the whole index by one more application of the fixed-support theorem. [Effective bound](HosoyaCofactorSupport.lean)

For S = {2,3}, C₂ = 38 and C₃ = 189. The supported cofactor divides 54, and 6 cannot divide a self-dividing index. The remaining cofactors are 1, 2, 3, 9 and 27. Their obstruction products leave four possible outside primes after 5 is excluded. Each row below gives a multiple n of the indicated p with p dividing Uₙ but p² failing to divide Uₙ. The lifting theorem then excludes p² from every index-value gcd at that prime. [Reduction to four primes](LucasFibonacciOneOutsideIndices.lean) · [Kernel-checked witnesses and single-power exclusions](HosoyaExceptionalPrimeCertificates.lean)

| p | n | Uₙ modulo p² |
| ---: | ---: | ---: |
| 67 | 1,809 | 2,479 |
| 157 | 10,990 | 6,751 |
| 6,719 | 181,413 | 11,025,879 |
| 6,983 | 188,541 | 41,381,258 |

Independent modular doubling checked 31,600 cofactor formulas and 30,916 exact prime-power tests at primes through 401. Direct enumeration through index 300,000 found 1, 3 and 27. Lean 4.33.1 independently replayed ten modules. All 25 named axiom audits used only standard axioms. [Kernel replay instructions](../../README.md#replay)
