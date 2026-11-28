# Green 33 implies a lower bound for Erdős 840

If Green 33 holds, then `Erdos840.IsQuasiSidonConstant (Real.sqrt 2)`. For every integer interval `[1,N]` there is a set `B_N` with both limits

```text
|B_N| / √N → √2,
|B_N+B_N| / binom(|B_N|,2) → 1.
```

The target is the definition imported from the pinned Erdős 840 file. Its asymptotics run over all natural numbers. The hypothesis is the full pinned Green 33 predicate, which asks for arbitrarily large cyclic moduli at each tolerance. This is a conditional lower bound for the Erdős–Freud constant. Its exact value and the existence statement in Green 33 remain open. [Lean proof](Green33QuasiSidon.lean) · [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Pinned Erdős 840](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/840.lean)

## Finite transfer

Let `m(k)` be the largest order of a cyclic group admitting a strict two-sum cover with at most `k` labels. The unconditional theorem `finite_transfer` gives a set `B ⊆ [1,N]` with exactly `k` elements and at least `m(k)` distinct integer sums whenever `k ≤ N` and `binom(k,2) ≤ N`. Thus the number of repeated unordered representations beyond the first is at most `binom(k+1,2) − m(k)`, with diagonal pairs counted once. [Maximal cyclic orders](MAXIMAL-ORDERS.md) · [Pair-count conventions](APPROXIMATE-COVERS.md)

A maximizing strict cover has modulus `M ≤ binom(k,2)`. Lift each label to its least nonnegative representative plus one. The resulting elements lie in `[1,M]`. Reducing an integer pair sum minus two modulo `M` recovers every residue, so there are at least `M` different integer sums. Padding the lifted set within `[1,N]` to reach size `k` preserves this inequality.

Take `k=⌊√(2N)⌋`. Under Green 33 the all-budget theorem gives `m(k)/k² → 1/2`, so `m(k)/N → 1`. The finite transfer bounds the integer sumset between `m(k)` and `binom(k+1,2)`. Both endpoints and `binom(k,2)` are asymptotic to `N`. This supplies one interval set at every `N`, even when Green’s original witnesses occur at sparse moduli. [Graham–Sloane limit](MAXIMAL-ORDERS.md)

Erdős and Freud’s unconditional lower constant is `2/√3`. Pikhurko’s unconditional upper constant is approximately `1.863`. The conditional `√2` lies strictly between them. The implication uses neither published bound. [Erdős–Freud, *On sums of a Sidon-sequence*](https://www.sciencedirect.com/science/article/pii/0022314X9190083N) · [Pikhurko, *Dense edge-magic graphs and thin additive bases*](https://pikhurko.github.io/E/Pikhurko06dm.pdf)

Open Math Agents contributors have formalized the unconditional Erdős–Freud lower bound and proposed a shorter proof. A DeepMind pull request collects external proof links for the construction. [Merged lower-bound proof](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1478) · [Shorter proof](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/11577) · [DeepMind proof links](https://github.com/google-deepmind/formal-conjectures/pull/8281)

Both public declarations print only `propext`, `Classical.choice` and `Quot.sound`. The proof imports Erdős 840 for its definition. Its open and admitted theorems supply no proof steps. Codex assisted with the formalization. [Replay instructions](../README.md#replay)
