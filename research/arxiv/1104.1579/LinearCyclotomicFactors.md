# Cyclotomic factors of Jones chains from a linear seed

Take a positive integer a, an integer b and a sign ε = ±1. Start at T₀ = aX+b and set Tₙ₊₁ = XTₙ+ε, as in Jones’s polynomial Cunningham chains. The following tables give every cyclotomic order d ≥ 1 for which Φ_d divides Tₙ over ℚ, for **every n ≥ 0**. [Lean classification](CunninghamLinearCyclotomicFactors.lean) · [Jones’s definition and examples](https://arxiv.org/pdf/1104.1579#page=2)

| Order | Exact condition for either sign |
| --- | --- |
| 1 | a+b+εn = 0 |
| 2 | b = a at even n, or b = a+ε at odd n |

For d > 2, every possibility has ε = +1. The complete list has five seeds.

| Seed | Order d > 2 | Indices |
| --- | --- | --- |
| X+1 | Any d > 2 | d divides n+2 |
| X | 4 | n ≡ 1 modulo 4 |
| X−1 | 6 | n ≡ 1 modulo 6 |
| 2X−1 | 6 | n ≡ 2 modulo 6 |
| 2X | 6 | n ≡ 3 modulo 6 |

Consequently the two signs **both avoid all cyclotomic factors at every positive index** exactly for the seeds a(X−1) with a ≥ 2. Indeed if a+b ≠ 0, the sign opposite to a+b supplies the root 1 at index |a+b|. When b = −a and a = 1, the first-kind successor is Φ₆. For a ≥ 2 the tables exclude every order. Noncyclotomic factors can still occur.

## The degree-two restriction

Set G(X) = (X−1)(aX+b)+ε. Telescoping gives (X−1)Tₙ = XⁿG−ε. If z ≠ 0,1 and both z and its inverse are roots of Tₙ, multiply the two equations to get G(z)G(1/z) = 1. Clearing denominators and cancelling (z−1)² gives

```text
a(ε−b)(z²+1) + ((a+b)ε−a²−b²)z = 0.
```

The quadratic vanishes identically only at ε = a = b = 1. That seed gives Tₙ = 1+X+⋯+Xⁿ⁺¹. In every other case the primitive root and its inverse have the same cyclotomic minimal polynomial, so φ(d) ≤ 2. Its only possibilities are d = 1, 2, 3, 4, 6. [Reciprocal root identity and totient argument](CunninghamLinearReciprocalRoots.lean)

At orders 3, 4 and 6 a primitive root satisfies z²−sz+1 = 0 for s = −1, 0 and 1 respectively. For the positive sign, work backwards from zero. If the coefficients required at a step are (u,v), those required one step earlier are (1−v,u+s(v−1)). The pair starts at (0,0), and the residue of n modulo d suffices. Since 1 and z are rationally independent, the resulting coefficients are necessary as well as sufficient. Switching the sign negates both. [Finite cases and endpoint checks](CunninghamLinearCyclotomicFactors.lean)

The pinned DeepMind predicates concern the primality of natural numbers under 2p±1, with failure at the first excluded term. The classification above concerns polynomial factors under Xf±1 and leaves both integer infinitude questions open. [Pinned source](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean) · [Polynomial specialization at 2](PolynomialLengths.md)

Lean 4.33.1 rebuilt and independently kernel-replayed three notebook modules. The 13 named axiom reports used only `propext`, `Classical.choice` and `Quot.sound`. A separate integer-polynomial calculation tested both signs, 1 ≤ a ≤ 7, −8 ≤ b ≤ 8, 0 ≤ n ≤ 32 and 1 ≤ d ≤ 32. Exact division gave 687 positive tests out of 251,328, all agreeing with the tables. [Notebook replay](../../README.md#replay)
