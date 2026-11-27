# Arbitrarily long prime prefixes suffice for Jones's conjectures

For each kind of Cunningham chain separately, the following statements are equivalent.

1. For every positive `k`, infinitely many seeds start a chain of exact length `k`.
2. For every `L`, some seed has prime terms at all indices `0 ≤ i < L`.

The second statement asks for a single witness at each length and places no condition on its next term. The equivalence is unconditional. Existence of arbitrarily long prime prefixes for either kind remains open. [Lean proof](CunninghamUnboundedPrefixes.lean) · [Jones, §1](https://arxiv.org/pdf/1104.1579)

**Termination.** For an odd prime seed `p`, write the recurrence modulo `p` as `t(i+1) = 2t(i) + c`, with `c` equal to 1 or −1. Then `t(i) + c = 2^i c` modulo `p`. Fermat's little theorem gives `p ∣ t(p−1)`. This term exceeds `p`, so it is composite. For the seed 2, the first kind stops at index 5 and the second at index 3. The fixed second-kind seed 1 cannot start a positive prime prefix.

**Exact length and infinitude.** Given a desired length `k > 0` and seed bound `B`, choose a prime prefix of length `B + k + 1`. Follow it to the first nonprime term at index `N`. The term at index `N−k` starts an exact length-`k` chain. The terms strictly increase, and `N−k > B`, so the resulting seed exceeds `B`. Conversely, exact chains of unbounded lengths give arbitrarily long prime prefixes.

The two declarations `CunninghamChain.firstKind_infinitude_iff_unbounded_prefixes` and `CunninghamChain.secondKind_infinitude_iff_unbounded_prefixes` take their left sides directly from the pinned upstream declarations with `type_of%`. A third declaration, `CunninghamChain.both_nonprime_at_pred_of_odd_prime`, records the explicit termination bound. The earlier notebook proofs derive exact-length infinitude from Dickson. These equivalences import only the upstream Cunningham module. [Pinned predicates and conjectures](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean) · [first-kind Dickson implication](../NOTES.md) · [second-kind Dickson implication](CunninghamSecondKindDickson.md)

Open and closed DeepMind and OMA searches located the original statement, the reductions separating length one, and an OMA statement for the different recurrence `2p + 13`. No matching Lean equivalence appeared in those searches or the LTS solved list. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/4755) · [first-kind reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8693) · [second-kind reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8706) · [generalized recurrence](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8945) · [LTS solved records](https://lefttosolve.com/api/solved)

Replay in the [pinned Lean 4.33.1 environment](../../README.md#replay) with `lake env lean "$notebook/arxiv/1104.1579/CunninghamUnboundedPrefixes.lean"` from the Formal Conjectures checkout. The file prints the axioms of all three results. Codex assisted with the formalization.
