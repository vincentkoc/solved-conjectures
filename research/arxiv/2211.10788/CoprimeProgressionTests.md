# Progression tests avoiding prescribed prime divisors

Fix an integer candidate y, a positive step d and a nonnegative offset r. Write U(w) = 2F_w+F_{w+2} for the bilateral upper Hosoya sequence. Given any positive B, one can decide whether U(w)=y for some integer w ≡ r modulo d using a single **odd modulus coprime to B**. In particular, removing every modulus divisible by even one prime factor of B leaves the exact congruence closure on the progression. [Main Lean proof](LucasFibonacciCoprimeProgressionTests.lean) · [Earlier single-modulus test](IndexProgressionClosure.md)

## Constructing the tests

Let b = 1 + ⌊log₂(20y²+40000)⌋. At level e ≥ 0 put H = 4db·4ᵉ. Let L_h denote the ordinary Lucas numbers and let O_h = L_h/gcd(2,L_h). Define

```text
Mₑ = O_H O_{2H}.
```

Each Mₑ individually gives an exact test. An index w in the prescribed class with U(w)=y exists if and only if U(r+dt) ≡ y modulo Mₑ for some 0 ≤ t < 32b·4ᵉ. A successful test recovers a witness with |w| < H. The number of progression terms to inspect is independent of d and r, though the modulus depends on d. Distinct Mₑ are pairwise coprime. Writing ω(B) for the number of distinct prime factors of B, at least one level from 0 through ω(B) has gcd(Mₑ,B)=1. [Dyadic Lucas numbers](HosoyaDyadicLucasNumbers.lean) · [Coprimality and finite avoidance bound](HosoyaCoprimeLucasTower.lean)

## Why the sign is determined

Modulo L_H, translation by 2H sends U to −U. The same holds modulo O_H. In the interior of the centered window, 4|U(w)| ≤ L_H, enough to lift a congruence even when a factor of two was removed. The end corrections from the earlier proof exclude the remaining six positions at each end. A hit modulo O_H therefore gives an exact value up to sign and an index congruent to the input modulo 2H. At the next scale O_{2H} it gives an index congruent to the same input modulo 4H. Both exact values have magnitude |y|, so the Fibonacci lower bound forces both indices strictly between −H and H. They agree modulo 2H and hence agree as integers. The input is now a multiple of 4H from that index, which preserves the sign already at the first scale. [Window bounds](HosoyaLucasWindowBounds.lean) · [Lift up to sign](HosoyaProgressionDetection.lean) · [Two-window lift](HosoyaTwoWindowLift.lean)

For even h, L_{2h} = L_h²−2. No such doubled value is divisible by four. If an odd prime divides one term of the dyadic tower of Lucas numbers, the following residues are −2, 2, 2, … modulo that prime. It can divide just one level. Grouping disjoint pairs of levels gives the pairwise coprime odd moduli above. The period 8H explains the stated finite search bound.

## Scope and prior work

Bartolome, Bilu and Luca proved the exponential local-global principle for rank-one power sums over rings of S-integers. The power sum U(r+dt)−y belongs to that setting: its two nonconstant bases are powers of the golden ratio and its negative inverse. The contribution here is an elementary kernel-checked construction of a pairwise coprime sequence of detecting moduli, with explicit bounds on the level and number of terms. Ching et al. and the pinned DeepMind statement ask whether the nonnegative-index sequence has infinitely many distinct prime values. Candidate membership on an index progression leaves that question open. [Bartolome, Bilu and Luca, Theorem 1.2](https://doi.org/10.4064/aa159-2-1) · [Ching et al.](https://arxiv.org/abs/2211.10788) · [Pinned DeepMind declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean)

An independent recurrence calculation checked the complete 8H modular periods at levels 0, 1 and 2 for every candidate from −100 through 100 and every offset class for steps 1 through 8. All 21,708 candidate, class and level combinations matched the exact bilateral witnesses. Each sampled tower had mutually coprime odd detectors. A clean Lean 4.33.1 build and independent kernel replay checked eleven notebook modules. All 43 named axiom reports used only standard axioms. [Kernel replay instructions](../../README.md#replay)
