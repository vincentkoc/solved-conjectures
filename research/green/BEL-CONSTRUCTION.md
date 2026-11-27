# Green 33 · an explicit cyclic two-basis

For every `q = 6n + 7`, there is an explicit basis of size `4q` in the cyclic group of order `N = 6q(q − 2)`. Its normalized size tends to `√(8/3)`. This formalizes the diameter-two construction of David Bevan, Grahame Erskine and Robert Lewis in *Large circulant graphs of fixed diameter and arbitrary degree*, Theorems 9 and 10(a). [Paper](https://arxiv.org/pdf/1506.04962#page=9) · [Lean proof](Green33BELConstruction.lean)

Write `p = q − 2`. The Chinese remainder theorem identifies the cyclic group with `Z/q × Z/p × Z/6`. The basis consists of these four sets.

| Label in Z/6 | First two coordinates | Parameter |
| --- | --- | --- |
| 0 | `(x, 0)` | `x ∈ Z/q` |
| 1 | `(0, y)` | `y ∈ Z/p` |
| 2 | `(t, t)` | `0 ≤ t < q + 2` |
| 4 | `(u, 2u)` | `0 ≤ u < q` |

Each pair of distinct labels covers its whole layer. In layer zero the summands have labels 2 and 4. To hit `(x,y)`, take the least residues `a = x mod q` and `b = (y − a) mod p`. For `b ≤ a`, choose `(t,u) = (a − b,b)`. For `b > a` and `b ≥ 2`, choose `u = b − 2` and `t = a + q − u`. The remaining case is `(a,b) = (0,1)`, for which `(t,u) = (3,p − 1)` works. The diagonal is injective on its indicated range because agreement in both coordinates implies congruence modulo `pq`.

**Comparison with Green 33.** The declaration `frequently_cyclic_basis` uses the positive moduli, frequency quantifier, sumset equality and absolute-error test in the upstream statement. The change is the constant, from `√2` to `√(8/3)`. The explicit ratio has square `(8/3)(1 + 2/p)`. Reaching `√2` remains open. [Pinned DeepMind declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Green, problem 33](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.33)

**Limitation.** The theorem `four_label_bound` checks the diameter-two label count from Observation 11. If every layer of a cyclic group of order `w` must be the sum of two distinct labels from a four-element set, then `w ≤ 6`. The construction attains six. This counting argument depends on the distinct-label hypothesis. [Observation 11](https://arxiv.org/pdf/1506.04962#page=10)

**Prior work and replay.** The DeepMind issue and merged PR record the problem statement. The LTS target and solved feed and the open and closed OMA trackers yielded no matching proof. The notebook replay compiles the file from source with Lean 4.33.1. All five public theorems print only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the formalization. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [LTS target](https://lefttosolve.com/api/problems/Green33.green_33) · [LTS solved feed](https://lefttosolve.com/api/solved) · [OMA tracker](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%22Green33%22) · [Replay instructions](../README.md#replay)
