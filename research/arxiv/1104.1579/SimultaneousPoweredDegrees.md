# Degrees shared by all powers of a Jones coefficient

Fix any integer base `m ≥ 2`. For a set of degrees `j` of natural density one, **every** positive exponent `h` gives an irreducible polynomial over ℚ,

```text
P(j,m^h) = X^j + X^(j−1) + ⋯ + X + m^h.
```

The density statement is uniform in the position of the interval. Given any `ε > 0`, there is a length `N₀` such that every interval of `N ≥ N₀` consecutive degrees contains fewer than `εN` degrees where some positive exponent fails. This gives upper Banach density zero for the exceptional degrees. The set in Lean also counts degree zero, where the polynomial is a nonzero constant. The declarations are `CunninghamChain.jones_all_powers_density_one` and `CunninghamChain.jones_powered_exceptional_windows`. [Lean proof](CunninghamJonesPoweredDensity.lean)

## Arithmetic of an exceptional degree

Put `C(m) = 2 · (m^(2m))!`. For positive `j,h`, reducibility of `P(j,m^h)` implies `m^h ∣ C(m)hj`. In particular the degrees `1 ≤ j < m^h/(C(m)h)` are all irreducible. The constant is a convenient common multiple. [Divisibility proof](CunninghamJonesPoweredDegrees.lean)

A factorization supplies positive coprime constants `u,v > 1` with `uv=m^h` and `u^(2j) ≡ 1 mod v`, and the same congruence with the factors exchanged. Coprimality gives `u=a^h`, `v=b^h` and `ab=m`. For a prime power `p^s ∣ b^h`, lifting the exponent in the complementary congruence gives `p^s ∣ (a^(2(p−1))−1) · 2hj`. The positive factor in parentheses divides `(m^(2m))!`. Exchanging the two factors accounts for every prime power of `m^h`. [Complementary congruences](CunninghamJonesComplementaryOrders.lean) · [Mathlib's lifting-the-exponent lemmas](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Multiplicity.html)

To see the effect on all exponents at once, prescribe any `k ≥ 0`. When `h ≥ 2(C(m)+k)`, the divisibility bound forces `m^k ∣ j`, since `2v_p(h) ≤ h` for every prime. The remaining exponents form a finite set. Each of their coefficients has a fixed cutoff above which every degree is irreducible. Thus **all sufficiently large exceptional degrees are multiples of `m^k`**, for each prescribed `k`. An interval of length `N` contains at most `D + ⌊N/m^k⌋ + 2` exceptional degrees, where `D` is the cutoff for this `m,k`. [Concentration theorem](CunninghamJonesPoweredDegrees.lean) · [Fixed-coefficient cutoff and published large-gap bounds](JonesLargeDegree.md)

## Scope

Jones’s Conjecture 4.1 asks for the exact exceptional degree for specified coefficients. The present theorem allows arbitrary bases and all their positive powers, and gives a density and divisibility restriction. It allows finite or infinite exceptional sets. For instance, at `m=6, h=1, j=3`, the polynomial factors as `(X+2)(X²−X+3)`. The pinned DeepMind declarations instead quantify over integer prime seeds and require exact termination at each prescribed chain length. Both prime-seed infinitude assertions and the general polynomial classification remain open. [Jones, §4](https://arxiv.org/pdf/1104.1579#page=7) · [Pinned integer-chain declarations](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean) · [Issue](https://github.com/google-deepmind/formal-conjectures/issues/4755) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/4765)

The notebook’s [prescribed multiplicities theorem](PrescribedPrimeMultiplicities.md) constructs bases for which every positive odd exponent works in every positive degree. Here the base is given in advance and even exponents are included. Codex assisted with the formalization. For focused replay, use `CunninghamJonesPoweredDensity`. [Notebook replay instructions](../../README.md#replay)
