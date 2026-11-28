# Growth of the Cunningham chain constant

Let Bₖ be the common Bateman–Horn Euler product for the first k terms of a Cunningham chain of either kind. As k tends to infinity,

```text
log Bₖ = k log log k + O(k).
```

In particular, the ratio of log Bₖ to k log log k tends to one. These assertions about the constant are unconditional. Proposition 1.7 of Kanado gives a lower bound for (log Bₖ)/k with leading term log log k, and an upper bound with leading term log k. The estimate here brings the upper bound down to the lower bound’s scale. [Lean proof](CunninghamSingularSeriesGrowth.lean) · [Kanado, Proposition 1.7](https://arxiv.org/pdf/2205.07650#page=3)

### What controls the upper bound?

At an odd prime p the number of forbidden residues is ν = min(k, ordₚ(2)). At 2 it is one. The local factor is (1 − ν/p)(1 − 1/p)⁻ᵏ. Consider primes p > k² with ν < k. Each divides some 2ʲ − 1 for 1 ≤ j < k, hence divides D = (2¹ − 1)⋯(2ᵏ − 1). Since D ≤ 2^(k²), it has at most k² distinct prime factors. Every finite set of these exceptional primes therefore satisfies ∑ 1/p ≤ 1. Their combined contribution to log Bₖ is at most 2k. The other primes above k² have ν = k and, by Bernoulli’s inequality, local factor at most one. [Local root counts and convergence](BatemanHornCounts.md)

For p ≤ k², dropping the numerator leaves the kth power of the finite product of (1 − 1/p)⁻¹. The proof bounds this product through z by 2 exp(4) log z for all sufficiently large z. It compares the factors at 1 and at 1 + 1/log z, using the bound 2 log z for the sum of (log p)/p over primes p ≤ z and Mathlib’s residue-one theorem for the Riemann zeta function. Thus the small primes contribute at most k log log k + O(k).

For the lower bound, the factors with p ≤ 2k retain the same denominator product and have numerator at least 1/p. The harmonic series bounds the inverse denominator product below by log(2k+1), and Chebyshev’s inequality bounds the sum of log p up to 2k by 2k log 4. Above 2k the logarithm of each local factor is at least −2k²/p². Summing the tail by telescoping costs at most k. Passing the finite bounds to the known positive limit gives, for all sufficiently large k,

```text
log log k − (2 log 4 + 1) ≤ (log Bₖ)/k ≤ log log k + 6 + log 4.
```

### Scope and replay

The pinned Jones predicates require prime terms at all indices below k and a nonprime term at k. The notebook’s earlier counting theorem takes the full Bateman–Horn conjecture as a hypothesis and gives Bₖ x/(log x)ᵏ as the asymptotic for exact chains at each fixed positive k. The present theorem determines the leading growth of **log Bₖ** as k varies. Both Jones infinitude conjectures remain open. Deducing a maximal chain length from a counting asymptotic would also require control of its error as k varies. [Pinned Jones predicates](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean) · [Pinned Bateman–Horn product](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Wikipedia/BatemanHornConjecture.lean)

The four declarations in `CunninghamChain` are `chainForms_exceptional_reciprocal`, `chainConstant_spec`, `chainConstant_log_bounds` and `chainConstant_log_asymptotic`. Each uses only `propext`, `Classical.choice` and `Quot.sound`. Searches of open and closed DeepMind and Open Math Agents issues and PRs and Left to Solve solved records found the Jones declarations and no matching formalization of the growth bound. Codex assisted with the formalization. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/4755) · [OMA search](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%22Cunningham%22+%22singular+series%22) · [LTS](https://lefttosolve.com/api/solved) · [Replay](../../README.md#replay)
