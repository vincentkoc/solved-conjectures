# Common divisors of an index and its upper Hosoya value

For the upper value Uₙ = Fₙ + Lₙ₊₁, the **only prime-power indices n > 1 for which n divides Uₙ are 3 and 27**. Here U₃ = 9. The classification concerns divisibility by the whole index. For arbitrary indices the following test determines exactly which powers of a prime can divide both index and value. [Prime-power classification and finite support bound](LucasFibonacciSelfDividingPrimePowers.lean) · [Pinned sequence and prime-values question](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean)

## One coefficient per prime

Let r be the least positive index at which p divides Fᵣ. In the ring with ω² = ω+1, let Cₚ be the coefficient of ω in (3+ω)ʳ. This is a positive integer. For each k ≥ 1 there exists n with pᵏ dividing gcd(n,Uₙ) **if and only if** p differs from 5 and 11 and pᵏ divides Cₚ. Thus for an ordinary prime, the largest attainable exponent is exactly the p-adic valuation of Cₚ, including zero when p never occurs. At an individual index the stronger formula is

```text
p ≠ 5 and p^(k−1) divides n  ⇒  (p^k divides Uₙ  iff  p divides Uₙ and p^k divides Cₚ).
```

In particular, every divisor of gcd(n,Uₙ) whose primes lie in a prescribed finite set S divides the explicit product of the Cₚ for p in S. Only finitely many indices supported on S can divide their own values. For example r₂ = 3 and C₂ = 38, while r₃ = 4 and C₃ = 189. A common divisor can contain 27, and none can contain 4 or 81. [Local equivalence and attainability](HosoyaIndexCommonDivisors.lean) · [Earlier test for divisors along fixed progressions](ProgressionDivisors.md)

## Why the test stops

The imaginary coordinate of (3+ω)ωⁿ is Uₙ. For an element scalar modulo p with invertible real coordinate, raising to a power coprime to p preserves divisibility of its imaginary coordinate by every power of p. Raising to the pth power gains at least one digit of p-adic divisibility. Both facts follow by expanding the two coordinates over the integers, including at p = 2. For p ≠ 5 the two Fibonacci roots are distinct in the algebraic closure of the residue field. Frobenius then shows that p divides F at index pᵉt precisely when it divides F at t. In particular p is coprime to its return rank r. [Coordinate lifting](HosoyaQuadraticPowerCoefficients.lean) · [Frobenius and prime-power ranks](HosoyaPrimePowerIndices.lean)

At an index divisible by p^{k−1}, ωⁿʳ is scalar modulo pᵏ with invertible real coordinate. In the identity ((3+ω)ωⁿ)ʳ = (3+ω)ʳωⁿʳ the right side therefore tests pᵏ against Cₚ. At a hit modulo p the tame-power calculation on the left tests it against Uₙ itself. Conversely the earlier prime-level progression theorem supplies a hit on a multiple of pᵏ when p divides Cₚ and p differs from 5 and 11. Five hits only at indices congruent to 2 modulo 5, and eleven never divides the sequence. At a prime-power index pᵉ, Frobenius fixes or exchanges the two Fibonacci roots, leaving U congruent to 4 or −3 modulo p. This leaves only 2 and 3 as candidate bases for self-divisibility. The two coefficient bounds reduce their exponents to a finite check.

Mastrostefano and Sanna prove density results for level sets of the gcd of an integer recurrence and a polynomial in its index. Moree and Stevenhagen study the density of primes dividing some term of this same shifted Lagarias sequence. Here the local criterion computes which multiplicities can occur in common with the index. The canonical question asks for infinitely many distinct primes equal to upper values, which remains open. [Mastrostefano and Sanna](https://doi.org/10.1017/S0004972718000606) · [Moree and Stevenhagen](https://arxiv.org/abs/math/9912253) · [Ching et al.](https://arxiv.org/abs/2211.10788)

An independent modular recurrence checked all 7,704 local cases for ordinary primes below 120, the first four levels, and multipliers from zero through twice the return rank. Among 9,590 ordinary primes through 100,000, exactly 5,565 passed the prime-level test and only 3 passed the square-level test. Direct enumeration through index 15,000 found self-divisors 1, 3 and 27. The theorem classifies all prime-power indices and leaves the unrestricted self-divisor list open. Lean 4.33.1 independently replayed five modules. All twelve named axiom audits used only standard axioms. [Kernel replay instructions](../../README.md#replay)
