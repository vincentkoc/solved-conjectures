# Green 33 · lifting a strict sum cover

For each integer `n ≥ 0`, put `s = 27720`, `Q = s(n+1) + 1` and `N = 56Q²`. There is a cyclic two-basis of size exactly `12(Q+s)` modulo `N`. Its size divided by `√N` tends to `12/√56 = √(18/7)`. The same frequency and error quantifiers as in Green 33 therefore hold at this constant. Green asks whether `√2` is attainable. [Lean proof](Green33StrictCoverLift.lean) · [Pinned statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

## Construction

Use Haanpää’s twelve labels `L = (0,1,12,15,22,29,32,43,44,48,50,52)` in `Z/56`. Every residue is the sum of two distinct labels. The Lean kernel checks the 56 cases directly. Since `Q ≡ 1 (mod 56)`, CRT identifies `Z/N` with `Z/Q² × Z/56`. For `0 ≤ i < 12` and `0 ≤ t < Q+s`, take the points `((s+iQ)t, Lᵢ)`. Each weight is a unit modulo `Q²`, the progression is shorter than the modulus, and different labels separate the progressions. This gives the exact cardinality. [Haanpää, *Minimum Sum and Difference Covers of Abelian Groups*, table 4](https://cs.uwaterloo.ca/journals/JIS/VOL7/Haanpaa/haanpaa.pdf#page=9)

Fix a pair of indices `i < j` and a target first coordinate `x`. Write `d = j−i` and `h = s/d`, which is integral since every integer from 1 through 11 divides `s`. Choose `0 ≤ a,v < Q` with

```text
x       = sa + Qb
b−ia−s  = dv + Qe.
```

These expansions exist because `Q` is one more than a multiple of both `s` and `d`. The coefficients below cover the two possible carries.

| Condition | First coefficient t | Second coefficient u |
| --- | --- | --- |
| v+h ≤ a | a−v−h | v+h |
| a < v+h | a+Q−v | v |

Both coefficients are in `[0,Q+s)`. In the first case, `t+u = a` and `ia+du = b−Qe`. In the second, `t+u = a+Q` and `ia+du = b−s−Qe`. In either case, `(s+iQ)t + (s+jQ)u ≡ x (mod Q²)`. Thus each distinct pair of progressions covers its entire sum layer.

## Comparison and replay

The squared constant `18/7` is smaller than `8/3` from the Bevan–Erskine–Lewis family by `2/21`. The two constants describe explicit infinite families. Optimality of the new family and the original Green question remain open. [Bevan–Erskine–Lewis, theorem 10(a)](https://arxiv.org/pdf/1506.04962#page=9) · [Notebook formalization](BEL-CONSTRUCTION.md)

The proof imports Mathlib on the notebook’s pinned toolchain. It includes axiom reports for the two-progression lemma, sumset coverage, cardinality, ratio limit and the frequency theorem. Codex assisted with the proof. [Replay instructions](../README.md#replay)
