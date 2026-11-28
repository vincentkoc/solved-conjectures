# Translation overlaps in asymptotically optimal cyclic bases

Suppose `M → ∞`, `|A|/√M → √2` and `|A+A|/M → 1` for sets in cyclic groups of order `M`. The largest **nonzero difference** multiplicity is `o(√M)`. Equivalently, the intersection of `A` with any nontrivial translate contains a vanishing fraction of its labels, uniformly over translations chosen after seeing the set. For full bases this gives a necessary condition on every family at the size in the pinned Green 33 question. The maximum **sum** multiplicity in such a family tends to infinity by the earlier divergence theorem. [Lean proof](Green33TranslateOverlap.lean) · [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Sum multiplicities](DIVERGENCE.md)

## Finite inequality and sharpness

In any abelian group take a finite set `A` of size `k`. Let `E = binom(k+1,2) − |A+A|` count excess unordered pairs, including diagonals once. For any nonzero shift `t`, write `b = |{x ∈ A : x+t ∈ A}|`. Then

```text
b(b−1) ≤ 4E.
```

Take two distinct starts `x,y` counted by `b`. The unordered pairs `{x+t,y}` and `{x,y+t}` are distinct and have the same sum. At most two ordered choices of `(x,y)` give a specified first unordered pair. Each sum of multiplicity `u ≥ 2` involves `u ≤ 2(u−1)` unordered pairs. Summing the two bounds proves the inequality.

The factor four is best possible over cyclic groups of arbitrarily large order. Take all lifts of a cyclic Sidon set of size `n` from order `M` to order `2M`. Translation by the involution preserves all `2n` labels. Each occupied sum downstairs gives two occupied sums upstairs, so the excess is exactly `n²`. Hence `b(b−1)/E = 4−2/n`. Ruzsa’s cyclic Sidon seeds supply unbounded `n`. [Cyclic seeds](SIDON-QUOTIENT-PROFILE.md) · [Ruzsa construction in Caicedo et al., §3](https://arxiv.org/pdf/1411.5741#page=7)

## Reflection centers

Let `D` be the largest nonzero difference multiplicity and `r(s)` the ordered sum count. For any finite set `C` of centers,

```text
∑_{s∈C} r(s) ≤ k + binom(|C|,2)D.
```

Indeed, the labels participating at two distinct centers `s,t` inject into the starts for shift `t−s`. The union of all participant sets lies inside `A`. Bounding pairwise intersections gives the estimate. In the near-optimal family above, `E=o(M)`, so the sharp finite inequality gives `D=o(√M)`. For every fixed center budget, the total ordered representation mass on those centers is at most `(√2+o(1))√M`, uniformly over the chosen centers. The existence of Green’s full bases remains open. [Approximate-cover equivalence](APPROXIMATE-COVERS.md) · [Reflection at finite equality](REFLECTION-RIGIDITY.md)

Erdős and Freud studied the closely related condition of nearly all integer pair sums being different. The finite estimate here uses the excess of ordinary unordered **sums** and measures the largest individual **difference**. It assumes neither an interval nor a density bound on the whole difference set. The seven public Lean declarations print only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the formalization. [Erdős–Freud, *On sums of a Sidon-sequence*](https://www.sciencedirect.com/science/article/pii/0022314X9190083N) · [Replay instructions](../README.md#replay)
