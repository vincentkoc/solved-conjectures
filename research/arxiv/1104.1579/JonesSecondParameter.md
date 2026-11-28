# Degree five is the only exception for Jones’s polynomial with constant 22

For every positive integer j, the polynomial `Pⱼ(X) = Xʲ + ⋯ + X + 22` is irreducible over ℚ if and only if `j ≠ 5`. At the exception it factors as

```text
P₅(X) = (X+2)(X⁴−X³+3X²−5X+11).
```

Jones’s Conjecture 4.1 sets `t = 2⌈(k+1)/2⌉+1` and `m = 2(2ᵗ+1)/3`. Both k = 2 and k = 3 give t = 5 and m = 22. Jones asks about j ≥ 3 for k = 2 and j ≥ 2 for k = 3. The theorem covers both ranges. The notebook previously settled k = 1. The general polynomial classification and the pinned conjectures on infinitely many integer prime seeds of each exact chain length remain open. [Lean theorem](CunninghamJonesSecondParameter.lean) · [Jones, Conjecture 4.1](https://arxiv.org/pdf/1104.1579#page=7) · [First parameter](JonesLargeDegree.md) · [Pinned chain predicates](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean)

## Why a finite certificate covers every degree

Suppose Pⱼ is reducible. The complementary factor result gives `j ≡ 5 mod 30` and a monic factorization Pⱼ = AB over ℤ with A(0) = 2 and B(0) = 11. Write B* for the polynomial with its coefficient list reversed and put H = AB*. Its coefficients h₀ through hⱼ have endpoints 2 and 11. Reflection preserves evaluation at 1, so their sum is j+22. Multiplying H by its own reflection gives the same product as multiplying Pⱼ by its reflection. The central coefficient therefore gives `Σ hᵢ² = j+484`. Combining these identities gives a degree-independent bound

```text
Σ (hᵢ−1)² = 441.
```

The endpoints spend 101 of this total. After reading n coefficients from each end, the coefficient of degree n in the reflected product is `22+n` for n < j. The known interior products leave a linear equation `11x+2y = T` for the next low and high coefficients. Their cost is `(x−1)²+(y−1)²`. Since the remaining budget is at most 340, the high coefficient lies between −17 and 19. Consequently all possible x lie among eight consecutive integers beginning at `⌊(T−38)/11⌋`. Each determines at most one y. [Complementary factor constants and degree congruence](JonesComplementaryOrders.md) · [Related reflected-product method of Sawin, Shusterman and Stoll, §§3–6](https://arxiv.org/pdf/1803.10811)

The coefficient count j+1 is even. If the two ends have reached each other, a degree above five requires n > 3, `2n ≡ 6 mod 30`, zero remaining budget and sum `2n+21`. Otherwise a polynomial witness supplies one of the enumerated children. The certificate proves that its root has no terminating descendant satisfying all four conditions. Induction maps every putative polynomial witness into this search, independently of its degree. [Finite certificate](CunninghamJonesTwentyTwoCertificate.lean) · [Induction and final classification](CunninghamJonesSecondParameter.lean)

## Verification

The declaration is `CunninghamChain.jones_second_parameter_irreducible_iff`. Lean 4.33.1 compiled the pinned source and seven notebook modules in a fresh directory. Each notebook module passed a separate kernel replay. All 25 named axiom reports use only `propext`, `Classical.choice` and `Quot.sound`. The finite certificate itself uses only `propext` and `Quot.sound`. [Notebook replay](../../README.md#replay)
