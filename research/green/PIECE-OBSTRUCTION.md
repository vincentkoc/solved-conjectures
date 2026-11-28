# Green 33 · bases covered by sets with small self-sumsets

Let a cyclic two-basis of size `k` modulo `q` be covered by `r` sets `Pᵢ`. Write `D = ∑ᵢ |Pᵢ+Pᵢ|`. Then

```text
2rq + k² ≤ rk² + 2rD.
```

The pieces may overlap and extend beyond the basis. The finite theorem `cover_count` holds in any additive commutative monoid with `|A+A|` in place of `q`. Assign each basis element to one covering piece. If the resulting disjoint parts have sizes `kᵢ`, sums from different parts occupy at most `∑ᵢ<ⱼ kᵢkⱼ` positions. Sums within parts occupy at most `D`. Apply `k² ≤ r∑ᵢ kᵢ²`. [Lean proof](Green33PieceObstruction.lean)

For fixed `r ≥ 2`, if `D/q → 0` and `k/√q → L`, then `L ≥ √(2r/(r−1))`. This excludes every such family from attaining Green’s proposed constant. For one piece the hypotheses are inconsistent. The theorem uses the pinned problem’s positive moduli and ordinary sumset equality. The cover and its small self-sumsets are additional hypotheses. Green’s question for unrestricted bases remains open. [Pinned DeepMind statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Green, problem 33](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.33)

For a basis that is a union of `r` arithmetic progressions, the hypothesis `D/q → 0` follows when `r` is fixed, `q → ∞`, and `k/√q` converges. Each self-sumset is contained in the union of the translates of the progression by its two endpoints, even when it wraps around. Thus `D ≤ 2rk`. For four progressions the constant `√(8/3)` is sharp. Bevan, Erskine and Lewis attain it with four cyclic progressions. Their Observation 11 bounds the number of layers obtainable from distinct generator types. Here the estimate applies directly to the sets in the cyclic group, including progressions with overlapping supports. [Construction and four labels](BEL-CONSTRUCTION.md) · [Bevan–Erskine–Lewis, Theorem 10(a) and Observation 11](https://arxiv.org/pdf/1506.04962#page=9)

There is also a finite consequence when `r` varies. Under `k² ≤ 2q+Ck` and `D ≤ Kk`, one has `k ≤ r(C+2K)`. For example, a partition into progressions satisfies the second hypothesis with `K=2`.

All five axiom reports use only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the formalization. [Replay instructions](../README.md#replay) · [DeepMind statement issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [LTS target](https://lefttosolve.com/api/problems/Green33.green_33) · [OMA tracker](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%22Green33%22)
