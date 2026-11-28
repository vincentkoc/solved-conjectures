# Prime parameters on the upper Hosoya diagonal

Write `U(n) = Fₙ + Lₙ₊₁ = 2Fₙ + Fₙ₊₂`. If both n and U(n) are prime, then **n is 2 or 5, or n is 41 or 89 modulo 120**. The two exceptional indices give U(2) = 5 and U(5) = 23. Of the 32 reduced classes modulo 120, precisely 41 and 89 have upper terms coprime to F₁₂₀. The normalized logarithmic Dirichlet mass of those two classes among prime indices is 1/16. The corresponding upper bound applies to prime-index prime values. Their infinitude and the pinned question about infinitely many distinct prime values at unrestricted indices remain open. [Lean sieve](HosoyaPrimeIndexSieve.lean) · [Mass bound](HosoyaPrimeParameterMass.lean) · [Pinned definition and question](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Ching et al.](https://arxiv.org/abs/2211.10788)

## The period-120 obstruction

For any L and n, the gcd of U(n) with F(L) equals the gcd of U(n mod L) with F(L). Every divisor of F(L) preserves upper-term divisibility under a shift by L, in both directions. Applying this fact to the two gcds proves equality. At L = 120 there are 32 reduced residue classes. In 30 of them one of 2, 3, 5, 23, 31 divides every upper term. These five primes divide F₁₂₀. For n ≥ 6 the term is at least 37, so this divisor is proper. At the remaining two classes the gcd is 1 even if every prime factor of F₁₂₀ is used. Other divisors can still occur there. For example, U(41) = 764654719 is divisible by 67. [Finite certificate and gcd theorem](HosoyaPrimeIndexSieve.lean)

The mass convention weights a prime parameter q by `log(q)/q^x`, sums over those parameters and multiplies by x−1 as x approaches 1 from above. A reduced class modulo 120 has limiting mass 1/32. The two surviving classes therefore have mass 1/16. For every c > 1/16 the normalized mass of the parameters where q and U(q) are both prime is eventually below c. [Analytic proof](HosoyaPrimeParameterMass.lean) · [Prime progression mass](../1104.1579/CunninghamPrimeDirichletMass.lean)

## Recurrence or a single prime hit

Fix any positive divisor modulus m and affine indices r+dt with r,d ≥ 0. Let e be the least positive t for which m divides F(dt). If m divides U(r+ds), it divides U(r+dt) exactly when t ≡ s modulo e, including t < s. When s and e are coprime, the prime hits form a reduced class and have mass 1/φ(e). Otherwise the only possible prime parameter is gcd(s,e). Testing that candidate distinguishes one hit from none. In particular, for every prime q,

- 463 divides U(q) exactly when q = 29. Its return rank is 464.
- 487 divides U(q) exactly when q = 61. Its return rank is 488.

The ordinary index classes in those examples contain infinitely many composite parameters. [Class theorem](HosoyaPrimeParameterClasses.lean) · [Checked singleton examples](HosoyaPrimeIndexSieve.lean)

For a prime divisor p there is also a finite test without a known starting hit. At p different from 5 and 11, put ω² = ω+1 and let C(r,k) be the coefficient of ω in `((3+ω)ωʳ)ᵏ`. Infinitely many prime parameters q satisfy `p ∣ U(r+dq)` if and only if

1. p divides C(r,e).
2. For every prime l dividing e, p does not divide C(r,e/l).

The first condition gives a hit. Restricting to parameters divisible by l changes the step from d to dl and divides the return rank by l. The second condition thus says exactly that the hit class is reduced. The general test also covers p = 5, where divisibility requires the physical index to be 2 modulo 5, and p = 11, which divides no upper term. In all cases the test gives limiting prime mass 1/φ(e) on success and zero on failure. This fixes the factor p and varies the prime parameter. Moree and Stevenhagen studied the density of factor primes when the index is unrestricted. [Order test](HosoyaPrimeParameterClasses.lean) · [Progression coefficient](ProgressionDivisors.md) · [Moree and Stevenhagen](https://arxiv.org/abs/math/9912253)

Lean 4.33.1 rebuilt and independently kernel-replayed six notebook modules. The 26 named axiom reports used only standard axioms from `propext`, `Classical.choice` and `Quot.sound`. An independent modular calculation checked 1,152 affine progressions at 48 divisor primes, including zero steps, and compared 125,568 prime-parameter instances with the predicted classes. Direct Fibonacci arithmetic checked all reduced residues modulo 120. [Notebook replay](../../README.md#replay)
