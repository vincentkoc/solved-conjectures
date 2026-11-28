# Erdős 864 would force an additive gap for cyclic two-bases

Assume the interval upper bound conjectured in Erdős 864. At every sufficiently large cyclic order `M`, every ordinary two-basis then has **more than `√(2M) + 1/10` labels**. The theorem takes the type of the pinned `Erdos864.erdos_864` declaration as its explicit hypothesis. Green 33 allows an additive error of order `o(√M)`, so even this strengthened necessary condition is compatible with a positive answer. [Lean proof](Green33Erdos864Extraction.lean) · [Pinned Erdős 864](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/864.lean) · [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

## Finite transfer

Every cyclic two-basis of size `k` modulo `M` gives an interval set `B ⊆ [1,M]` with at most one repeated unordered sum and

```text
|B| ≥ k − max(k²−2M,0) − 1.
```

This part is unconditional. Fix a center `s`. Keep all unordered pairs with sum `s`, and choose one witness for every other residue. From each remaining pair delete one endpoint. Every surviving sum outside the center has a unique unordered representation. If `r(s)` is the original ordered count, at least `r(s)/2` unordered pairs lie over the center, so the loss `d` satisfies `2d + r(s) + 2M ≤ k² + k + 2`. The finite reflection theorem supplies a center with `k − r(s) ≤ max(k²−2M,0)+1`. Integrality gives the claimed loss. [Finite reflection theorem](REFLECTION-RIGIDITY.md)

The wrap to an integer interval matters because one residue can lift to two integer sums. Translate by `−⌊s.val/2⌋`, take least nonnegative representatives, and add one to each label. Before adding one, the exceptional residue is zero or one. Either of those two small integer totals admits just one unordered pair of nonnegative summands. Thus the only integer sum that can repeat in the final interval is `M + (s.val mod 2) + 2`. The Lean conclusion uses `Erdos864.HasAtMostOneRepeatedSum` directly, including diagonal pairs.

## Quantitative conditional gap

Choosing a center of largest ordered multiplicity gives a stronger unconditional certificate for a retained size `b`. Write `u = k²−2M`. The deletion estimate and the centered energy bound give

```text
(k−1)(k−2) ≤ (u−k+2b+1)(u+k).
```

Put `v = √2` and `L = 2/√3`. The conjectured upper bound on `b` implies that for every nonnegative `c` satisfying `(c−v+2L)(c+v) < 2`, every sufficiently large cyclic two-basis has `u > c√M`. The positive endpoint is `√(L²+4−2Lv) − L ≈ 0.2831266451`. The Lean corollary uses `c = 283/1000` to obtain the displayed additive tenth. In particular, an unbounded family with `k²−2M = o(√M)` would refute the pinned Erdős 864 upper bound.

Erdős and Freud’s reflected Sidon construction gives the unconditional **lower** constant `2/√3` for interval sets. Existing Lean contributions formalize that construction. The implication here assumes the conjectured **upper** bound at that constant. Neither open conjecture is settled. [Erdős–Freud](https://www.sciencedirect.com/science/article/pii/0022314X9190083N) · [External construction formalization](https://github.com/laughingbear/erdos-sidon-constructions-lean) · [DeepMind proof-link PR](https://github.com/google-deepmind/formal-conjectures/pull/8281)

All six public theorems report only `propext`, `Classical.choice` and `Quot.sound`. The pinned file’s admitted declarations contribute no proof axioms to these results. Codex assisted with the formalization. [Replay instructions](../README.md#replay)
