# Simultaneous Jones degrees for smooth coefficients

Fix a prime bound `B`. There is a set of degrees of natural density one on which **every** rational polynomial

```text
Xʲ + Xʲ⁻¹ + ⋯ + X + m
```

is irreducible whenever `m ≥ 2` has at most three distinct prime divisors, all at most `B`. The primes and their multiplicities vary independently. For each `ε > 0`, every sufficiently long interval of length `N` contains fewer than `εN` degrees that fail for even one permitted coefficient. The two declarations are `CunninghamChain.jones_three_prime_density_one` and `jones_three_prime_exceptional_windows`. They have no external arithmetic hypotheses. [Density proof](CunninghamJonesSmoothDensity.lean)

For **all** coefficients with prime divisors at most `B`, the same conclusions are `jones_smooth_density_one` and `jones_smooth_exceptional_windows`. These take the fixed-support valuation estimate `JonesPadicLogBound B` as an explicit argument. The statement of that estimate, its source and its use are given below. The earlier result treats all powers of one fixed base with arbitrary prime support. [Earlier single-base theorem](SimultaneousPoweredDegrees.md)

## Why three primes suffice

Fix an exponent `k`. Suppose the degree `j` is positive and no prime power `pᵏ` for `p ≤ B` divides `j`. A factorization with coefficient `m ≥ 3` supplies coprime nontrivial constants `u,v` with `uv=m` and complementary congruences `u^(2j) ≡ 1 mod v` and `v^(2j) ≡ 1 mod u`. With three prime divisors available, one side must be a single prime power, say `u=pᵃ`. [Factorization lemma](CunninghamJonesComplementaryOrders.lean)

Lifting the first congruence prime by prime gives `v ∣ C a j` for `C=2·(B^(2B))!`. Every prime occurring in `v` has valuation less than `k` in `j`, so `v ≤ C(B!)ᵏa`. Lifting the other congruence gives `pᵃ ∣ 2j(v^(2(p−1))−1)`. Removing the same bounded contribution of `j` now yields `2ᵃ ≤ C' a^(2B)` for a constant depending only on `B,k`. This bounds `a`, hence `v` and `m`. The fixed-coefficient large-degree theorem disposes of all these bounded coefficients at once. [Complementary lifting](CunninghamJonesPoweredDegrees.lean) · [Boundedness proof](CunninghamJonesSmoothBounds.lean) · [Large-degree theorem and prior work](JonesLargeDegree.md)

It follows that, for every prescribed `k`, all sufficiently late exceptional degrees lie among multiples of some `pᵏ` with `p ≤ B`. In any interval of length `N`, the multiples of each such power contribute at most `⌊N/2ᵏ⌋+2` sites. Summing over the finitely many primes and then increasing `k` gives the uniform density conclusion. [Interval count](CunninghamJonesSmoothDensity.lean)

## The unrestricted support size

Write `L=2·B!`. For `v ≥ 2` with all prime factors at most `B`, the Lean hypothesis bounds every valuation of `vᴸ−1` at `p ≤ B` by

```text
K · (1 + ⌊log₂(1 + ⌊log₂ v⌋)⌋)
```

with one constant `K` depending only on `B`. This is the rational fixed-support consequence of Yu’s bound on p-adic logarithmic forms on page 242. Write `vᴸ` as the product of the fixed rational primes to exponents at most `L log₂ v`. Yu bounds the valuation of this product minus one by a fixed constant times the logarithm of the maximum of 3 and those exponents. The product is greater than one. An unused rational base with exponent zero may be included if only one prime occurs. Taking a maximum over the finitely many `p ≤ B` and absorbing the changes of logarithm base gives the displayed estimate. Yu’s analytic theorem is external to the replay. [Yu, *Linear forms in p-adic logarithms III*, §0.1](https://www.numdam.org/article/CM_1994__91_3_241_0.pdf#page=3)

Lean then bounds every smooth divisor of `vᴸ−1` by a polynomial in `1+log₂ v`. Take the larger side `u ≥ v` of a complementary factorization. Since every `p−1` for primes `p ≤ B` divides `B!`, the complementary congruence and lifting give `u ∣ 2j(vᴸ−1)`. If `j` avoids all the prescribed prime powers, this forces `u ≤ 2(B!)ᵏ gcd(u,vᴸ−1)`. The gcd is a smooth divisor, so its polynomial-in-log bound contradicts `u ≥ v` for large `v`. Bounded `v` also bounds `u`. This supplies the same finite-coefficient argument without a support-size restriction. [Valuation-to-divisor implication and proof](CunninghamJonesSmoothBounds.lean)

Jones’s Conjecture 4.1 specifies the exact exceptional degree at its particular coefficients. The pinned DeepMind declarations ask for infinitely many *integer* prime seeds with a prescribed exact termination length. Those questions remain open. Codex assisted with the formalization. For focused replay use `CunninghamJonesSmoothDensity`. [Jones, §4](https://arxiv.org/pdf/1104.1579#page=7) · [Pinned integer-chain declarations](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/4755) · [Replay instructions](../../README.md#replay)
