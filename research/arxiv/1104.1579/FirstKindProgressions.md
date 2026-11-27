# First-kind Cunningham chains in arithmetic progressions

Fix a modulus `d > 0`, a representative `r`, and a length `k > 0`. Write `Fᵢ(r)` for the first-kind term obtained by iterating `x ↦ 2x + 1`. Under Dickson's conjecture, infinitely many seeds congruent to `r` modulo `d` have **exactly** length `k` if and only if

```text
gcd(Fᵢ(r), d) = 1   for every 0 ≤ i < k.
```

If any test fails, there is **at most one** such seed, unconditionally. For example, the even class modulo 2 fails at index 0, yet the seed 2 has exact length 5. No coprimality condition on the stopping term `Fₖ(r)` is needed. [Lean proof](CunninghamFirstKindProgressions.lean) · [upstream definitions and length-five example](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean)

**Necessity.** The residue of `Fᵢ(s)` modulo `d` is fixed throughout the class. If its gcd with `d` exceeds one, the only possible prime value is that gcd itself. The term is injective as a function of the seed, so at most one seed survives.

**Sufficiency.** For primes dividing `d`, the prefix tests give local admissibility. For any other prime, choose the parameter so that the seed is congruent to −1. Every term then stays at −1. Dickson gives infinitely many prime prefixes. If the stopping term has a common factor with `d`, take a seed greater than `d` and the stopping term is composite. Otherwise apply the prefix argument one step further and choose a seed `b` whose term `q = Fₖ(b)` is prime. Restrict seeds to `b` modulo `d q`. The earlier terms at `b` are positive and strictly smaller than `q`, so the prefix tests still hold. The stopping term now has a fixed factor `q`.

`CunninghamChain.infinite_firstKind_chains_in_class_iff` takes the full type of the pinned Dickson declaration as a hypothesis and uses the original `IsFirstKindChainOfLength` predicate, including its nonprime stopping term. The modulus-one case recovers Jones's first-kind implication. `CunninghamChain.subsingleton_firstKind_chains_in_class_of_not_coprime` has no conjectural hypothesis. The unconditional infinitude question remains open. [Dickson declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Paper/PrimeTuples.lean) · [Jones, §1](https://arxiv.org/pdf/1104.1579) · [earlier notebook proof](../NOTES.md)

The DeepMind issue and PR concern infinitude without a prescribed residue. The OMA reduction splits off length one. Open and closed DeepMind and OMA searches by declaration, arXiv and OEIS identifiers, and progression terms, plus the LTS solved records, yielded no matching progression classification. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/4755) · [statement PR](https://github.com/google-deepmind/formal-conjectures/pull/4770) · [OMA reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8693) · [LTS solved records](https://lefttosolve.com/api/solved)

To replay in the [pinned Lean 4.33.1 environment](../../README.md#replay), run `lake env lean "$notebook/arxiv/1104.1579/CunninghamFirstKindProgressions.lean"` from the Formal Conjectures checkout. The file prints both axiom reports. Codex assisted with the formalization.
