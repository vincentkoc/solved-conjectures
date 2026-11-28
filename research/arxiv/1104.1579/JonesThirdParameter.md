# Degree seven is the only exception for Jones’s polynomial with constant 86

For every positive integer j, the polynomial Pⱼ(X) = Xʲ + ⋯ + X + 86 is irreducible over ℚ exactly when j ≠ 7. At j = 7 the factorization is

```text
P₇(X) = (X+2)(X⁶−X⁵+3X⁴−5X³+11X²−21X+43).
```

Jones’s Conjecture 4.1 takes t = 2⌈(k+1)/2⌉+1 and m = 2(2ᵗ+1)/3. Both k = 4 and k = 5 give t = 7 and m = 86. The conjecture asks about j ≥ 3 for k = 4 and j ≥ 2 for k = 5. The theorem covers both ranges unconditionally and also covers the smaller positive degrees. The earlier notebook results cover k = 1, 2 and 3. [Lean classification](CunninghamJonesThirdParameter.lean) · [Jones, Conjecture 4.1](https://arxiv.org/pdf/1104.1579#page=7) · [First parameter](JonesLargeDegree.md) · [Second parameter](JonesSecondParameter.md)

## Why the search covers arbitrarily large degrees

If Pⱼ is reducible then j ≡ 7 modulo 56 and Pⱼ = AB with monic integer factors having constant terms 2 and 43. This follows from the two multiplicative orders and the primality of 43. Reverse the coefficient list of B and multiply by A to obtain G. Its endpoints are 2 and 43. Its coefficients sum to j+86 and its product with its reversal equals the corresponding product for Pⱼ. Comparing central coefficients gives ∑(gᵢ−1)² = 85² for the coefficients gᵢ of G. Removing the endpoints leaves a budget of 5,460. The reflection and energy identities are proved for every constant term. [Degree congruence and factor constants](JonesComplementaryOrders.md) · [Reflection and energy](CunninghamJonesReflectedFactors.lean) · [Related reflected-product method of Sawin, Shusterman and Stoll](https://arxiv.org/abs/1803.10811)

Read n coefficients from each end. The coefficient of Xⁿ in the product with the reversal gives 43x+2y=T for the next pair, where T is determined by the two prefixes. The new pair consumes (x−1)²+(y−1)² of the remaining budget B. In particular, 1−⌊√B⌋ ≤ y ≤ 1+⌊√B⌋, so only a finite interval of x needs checking. The generic soundness proof shows that every possible polynomial supplies an enumerated child until the two ends meet. At that point B must be zero, the two prefix sums must add to j+86, and 2n=j+1. [Child enumeration](CunninghamJonesEndpointSearch.lean) · [Soundness for arbitrary positive endpoints and odd degrees](CunninghamJonesReflectedFactors.lean)

With endpoints 2 and 43, the search visits 15,370 states. No state extends past 40 pairs. The only lengths 2n congruent to 8 modulo 56 that occur are 8 and 64. At length 64 none of the 146 states meets the terminal conditions. The certificate excludes every terminal outside degree seven. Reaching the depth limit with an unexplored branch would make the check fail. The proof generator splits the search into subtrees, each checked by kernel reduction. [Finite certificate](CunninghamJonesEightySixCertificate.lean)

## Scope and sources

The pinned DeepMind declarations ask for infinitely many natural prime seeds at each exact chain length under the recurrences 2p+1 and 2p−1. They impose primality throughout the prefix and failure of primality at the next term. Both infinitude questions and Jones’s polynomial conjecture for general parameters remain open. The polynomial theorem uses no hypothesis about primes taken by polynomial values. [Pinned chain definitions and conjectures](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean)

Searches of open and closed DeepMind and OMA issues and PRs found the canonical integer-chain issue and the two statement PRs. The 4,526 LTS solved records included reductions for the integer infinitude statements. No matching formalization of the m = 86 polynomial classification appeared in these searches. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/4755) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/4765) · [Other statement PR](https://github.com/google-deepmind/formal-conjectures/pull/4770) · [LTS records](https://lefttosolve.com/api/solved)

Lean 4.33.1 rebuilt all nine notebook modules in the dependency closure. Each passed a separate kernel replay. All 30 named axiom reports use only `propext`, `Classical.choice` and `Quot.sound`. The certificate itself uses only `propext` and `Quot.sound`. The main declaration is `CunninghamChain.jones_third_parameter_irreducible_iff`. [Notebook replay](../../README.md#replay)
