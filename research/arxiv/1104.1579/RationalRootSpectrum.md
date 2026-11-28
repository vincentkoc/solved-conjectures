# Rational roots in the two Jones chains from a(X−1)

Fix the seed a(X−1) with a a positive integer. If a is any prime power, the complete list of rational roots at **all positive indices** of both polynomial Cunningham chains is as follows. Index zero is the seed.

| Coefficient a | Recurrence | Index n | Root |
| --- | --- | --- | --- |
| 4 | Xf + 1 | 1 | 1/2 |
| 4 | Xf − 1 | 3 | −1/2 |

For arbitrary positive a, let E(H) count the coefficients through H for which **any** positive iterate, for either sign, has a rational root. With L = ⌊log₂(4H+1)⌋ the bound is E(H) ≤ (L+1)(2L+3). In particular E(H)/H tends to zero. These conclusions apply to rational linear factors. The earlier finite-prefix theorem also excluded higher-degree factors within its range. The canonical DeepMind questions concern exact lengths of chains of natural primes under 2p ± 1 and remain open. [Prime-power classification](CunninghamPrimePowerRationalRoots.lean) · [Count and limit](CunninghamRationalRootDensity.lean) · [Earlier irreducible prefixes](FixedPrimePowerPrefixes.md) · [Pinned integer predicates](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean)

## The signed denominator

The constant term of a positive iterate is ε = ±1. The rational root theorem therefore writes each root as 1/d for an integer d. The values 0, 1 and −1 for d are excluded by the recurrence. Clearing denominators in the root equation gives an equivalence for |d| ≥ 2,

```text
Tₙ(1/d) = 0  ⇔  a(d−1)² = ε d²(dⁿ−1).
```

Moreover, d−1 divides n. Conversely, **every** signed integer d with |d| ≥ 2 and d−1 dividing n supplies a positive coefficient and a sign at index n. The coefficient is d²|dⁿ−1|/(d−1)² and the sign is the sign of dⁿ−1. To see the index condition, divide dⁿ−1 by d−1 and reduce the geometric sum modulo d−1. The result is n. [Root equation](CunninghamRationalRootDenominators.lean) · [Divisibility and converse](CunninghamRootCoefficientArithmetic.lean) · [Jones's polynomial recurrences](https://arxiv.org/abs/1104.1579)

Writing a = d²b gives gcd(|d|,b) = 1. At a prime power this forces b = 1, hence a = d². For ε = +1 the remaining equation gives dⁿ = d²−2d+2, so d divides 2. For ε = −1 it gives dⁿ⁻¹ = 2−d. Here n ≥ 2, so again d divides 2. Substituting d = ±2 yields the two entries above. [Denominator factorization](CunninghamRootCoefficientArithmetic.lean) · [Prime-power argument](CunninghamPrimePowerRationalRoots.lean)

For a ≤ H the same equation gives 2ⁿ ≤ |d|ⁿ ≤ 4a+1. Thus n ≤ L and |d−1| ≤ n. Counting the possible index and signed denominator pairs gives the bound on E(H). An independent search through H = 100,000 found 29 exceptional coefficients and the two prime-power cases listed above. It also compared the parametrization with 4,296 direct rational-root tests across coefficients 2 through 180, both signs and indices 1 through 12. A clean Lean 4.33.1 replay checked six modules and produced 18 named axiom reports within `propext`, `Classical.choice` and `Quot.sound`. [Finite bound and density theorem](CunninghamRationalRootDensity.lean) · [Kernel replay instructions](../../README.md#replay)
