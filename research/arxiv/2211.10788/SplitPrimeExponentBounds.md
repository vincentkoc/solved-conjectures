# Prime divisors of exponents in the neighboring product

Write `Uₙ=Fₙ+Lₙ₊₁` and `Vₙ=Fₙ+Lₙ₋₁`. For every physical index `n=m+2`, **if `UₙVₙ=yᵏ` with `k≥2`, every prime divisor of `k` is at least 101**. Equivalently, the product at that index is a proper power precisely when `6 ∣ n` and `yᵖ+1=11Fₙ²` for some natural `y` and prime `p≥101`. The earlier exact criterion had `p≥5`. The index-one product is 12. [Product theorems](HosoyaNeighborPowerExponents.lean) · [Earlier criterion](OddPowersAtNeighboringIndices.md)

The arithmetic result accepts any integer base `y`. At every positive multiple of six, `yᵖ+1 ≠ 11Fₙ²` for all 23 prime exponents from 5 through 97. The index bound matters since `n=0, y=−1` solves the equation for every odd exponent. [Finite certificates](HosoyaSmallExponentSieve.lean)

## A unit exponent shared by all the primes

Suppose `yᵖ+1=11f²`, with `f` even and `p>1` odd. In the norm-Euclidean ring ℤ[√11], the elements `1+f√11` and `1−f√11` have product `(−y)ᵖ`. Their common divisors divide their sum 2. Since `f` is even, each common divisor also divides 1. Factorization and the unit group therefore give

```text
1 + f√11 = (10 + 3√11)ⁱ vᵖ,     0 ≤ i < p.
```

If `i=0`, the real part of the odd power is 1. For `v=a+b√11` with `b≠0`, the real part of `v^(2t+1)` is `aA`. Multiplication by `v²` gives a recurrence in which `A>1` for `t>0`. Thus `b=0` and `f=0`. This leaves only nonzero unit exponents whenever `f` is a positive Fibonacci number. [Odd-power descent](HosoyaAuxiliaryPrime.lean) · [Euclidean division and units](HosoyaRealEleven.lean)

Choose a prime `q=kp+1` and a square root `r` of 11 modulo `q`. Substitution of `r` and `−r` gives two field equations with the same `i`. If `1±fr` is nonzero, its kth power must equal `((10±3r)ᵏ)ⁱ` by Fermat's little theorem. When both sides of the conjugate pair are nonzero, the two kth powers must multiply to 1. The certificate checks zero components separately. [Split-prime implication](HosoyaAuxiliaryPrime.lean)

For each prime exponent the certificate follows the Fibonacci pair at indices `6t` through a whole period modulo each chosen `q`. Lean verifies the return to `(0,1)`, every residue in the period, and the intersection of the allowed unit exponents. For example, at `p=43`, the prime 20641 allows the nonzero exponents 3 and 40. The prime 1549 allows 9, 19, 24 and 34. Only zero survives both tests. The proof uses the same exponent at both primes even at indices that are multiples of both periods. [General criterion](HosoyaExponentCertificates.lean) · [Certificate data](HosoyaSmallExponentSieve.lean)

## Scope

The product statements are `Arxiv.«2211.10788».neighboring_power_prime_divisor` and `neighboring_proper_power_large_exponent`. The general certificate theorem is `HosoyaAuxiliaryPrime.fib_power_excluded_of_rows`. The former conditional exclusion using the coefficient-eleven theorem of Bennett and Skinner applies to larger exponents as well. The results here use no external Diophantine hypothesis. [Earlier conditional argument](CubeNormAtEighteen.md) · [Bennett and Skinner, Theorem 1.1](https://doi.org/10.4153/CJM-2004-002-2)

The pinned DeepMind conjecture asks for infinitely many primes equal to an upper entry `Uₙ`. That question remains open. Codex assisted with the formalization. For focused replay use `HosoyaNeighborPowerExponents`. [Pinned statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Original paper](https://arxiv.org/abs/2211.10788) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [Replay instructions](../../README.md#replay)
