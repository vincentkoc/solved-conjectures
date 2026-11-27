# Green 33 · large representation counts survive deletions

Suppose cyclic two-bases `A` at moduli `q → ∞` satisfy `|A|/√q → √2`. Fix `α > 1` and a representation cap `M`. Eventually **every** subset `B ⊆ A` with at least `α√q` elements contains a sum having more than `M` ordered representations **inside `B`**. The subset can be chosen after seeing the basis, and its sumset need not cover the group. Thus deleting fewer than `(√2 − 1 − ε)√q` elements, for fixed positive `ε`, cannot keep the remaining representation counts bounded. [Lean proof](Green33HereditaryTail.lean)

**Quantitative bound.** For any two-basis in a finite abelian group of order `q`, put `k = |A|`, `b = |B|` and `δ = k² + k − 2q`. Write `r_B(s)` for the number of ordered pairs of elements of `B` summing to `s`, and `T(B,M) = ∑_{r_B(s)>M} r_B(s)²`. Then

```text
T(B,M) + Mδ ≥ 2b² − 3b + 2 − 2q.
```

Consequently for any `c < 2α² − 2`, eventually all such subsets have `T(B,M) > cq`. The same conclusion holds for a varying cutoff `M` if `Mδ/q → 0`. The fixed-cutoff version follows because `δ/q → 0` at Green’s proposed density.

**Proof.** The nonnegative integer polynomial `(d−1)(d−2)` on difference counts gives a lower bound on the corresponding sum over ordered sum counts, by isolating the zero difference of `B`. For the ambient basis, write `e_A(s) = r_A(s) + d_A(s) − 2`, where `d_A` counts diagonal pairs. Then `e_A ≥ 0` and its total is `δ`. On sums below the cutoff, `r_B(r_B−2) ≤ M e_A` because `r_B ≤ r_A`. On the other sums use `r_B(r_B−2) ≤ r_B²`. Summing gives the displayed inequality. At `b ≥ α√q` the term `3b/q` tends uniformly to zero since `b ≤ k`. [Difference-count argument](Green33ReflectionRigidity.lean) · [Earlier tail estimate for the whole basis](TAIL-ENERGY.md)

**Upstream scope.** Green asks whether the hypothesized family exists. This result is conditional on such a family and quantifies uniformly over its subsets. It gives no conclusion at the endpoint `α = 1`. Li and Chen give related representation bounds for finite additive bases. [Pinned Green 33 declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Green, problem 33](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.33) · [Li and Chen](https://doi.org/10.1017/S0004972717000302)

**Verification.** The four theorems in `Green33HereditaryTail` and the three shared lemmas they reuse print only `propext`, `Classical.choice` and `Quot.sound`. A clean replay compiled the proof, its four dependencies and the three earlier Green modules that use reflection rigidity, then checked the compiled modules with Lean 4.33.1. The DeepMind issue and merged PR record the question. Open and closed OMA trackers, the LTS target and its solved feed yielded no matching formalization. Codex assisted with the proof. [Replay instructions](../README.md#replay) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [LTS target](https://lefttosolve.com/api/problems/Green33.green_33) · [LTS solved feed](https://lefttosolve.com/api/solved) · [OMA tracker](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%22Green33%22)
