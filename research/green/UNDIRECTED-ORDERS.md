# Green 33 · undirected circulants of diameter two

Let `CC(d,2)` denote the largest order of an undirected circulant graph of degree exactly `d` and diameter exactly two. Then `CC(d,2)/d²` converges as `d` ranges over all natural numbers. The limit `U` is positive and at most the ordinary cyclic sum-cover limit `S ≤ 1/2`. The proof gives an explicit expression for `U` from finite symmetric seeds. Its value and Green’s conjectured value of `S` remain unresolved here. [Lean proof](Green33UndirectedOrders.lean) · [Ordinary cyclic orders](MAXIMAL-ORDERS.md) · [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

A connection set `T ⊂ Z/M` excludes zero and satisfies `−T=T`. Its degree is `d=|T|`. Put `A=T∪{0}`. The theorem `two_steps_iff` identifies `A+A=Z/M` with reachability in at most two steps between every pair of vertices. Under this condition, diameter exactly two is equivalent to `d+1<M` because the graph then has two distinct nonadjacent vertices. The maximum is extended by zero when there is no eligible positive modulus. Green uses an ordinary sum basis and imposes no inversion symmetry. [Bevan–Erskine–Lewis, §1](https://arxiv.org/pdf/1506.04962#page=2)

## From one seed to all large degrees

For a seed of degree `d` and diameter at most two, define

```text
h(d) = d + 1 + 8(⌊√(d+1)⌋ + 1) + 1.
```

There is a constant `C` depending on the seed such that every `K≥C` satisfies `M(K−C)² ≤ h(d)² CC(K,2)`. In the lift, a pair of inverse labels contributes one direction with both signs. Reversing a finite progression translates it, so two different directions can still be used with either choice of sign. This covers all high digits over every label sum from different inverse pairs. [Rectangular progression lemma](DIVISIBLE-ORDERS.md)

The exceptional labels lie among zero, the doubles of seed labels, and sums with a self-inverse label. Their number is at most `3(d+1)+1`. Over them the proof uses a common low interval and a progression of high digits for each label. Take a rectangular modulus `p(p−1)` with `p` even, use step `bp` for the high digits, and include the negatives of both sets. Here `b=2(⌊√(d+1)⌋+1)`. With sufficiently large `p`, the low interval misses the nonzero involution of the lifted cyclic group. Every self-inverse element reduces to zero modulo the seed order. In the zero layer all high digits have odd order, so they also miss the involution.

Removing zero leaves a symmetric connection set. It can be padded to any affordable exact degree by adding unused inverse pairs, using the reserved involution if one further generator is needed. The widths lie in an arithmetic progression of fixed spacing. Choosing the largest affordable width gives the inequality for every sufficiently large `K`, including odd degrees.

It follows that `U = sup M/h(d)²` over all finite seeds of diameter at most two. The inequality above makes each seed efficiency a lower bound for the limiting inferior. Conversely, every nonempty extremal problem supplies a seed at that degree, and `h(d)/d → 1` gives the matching upper bound. Adjoining zero to a connection set gives an ordinary sum basis and proves `U≤S`.

## Literature and replay

Bevan, Erskine and Lewis define separate lower and upper limits at fixed diameter. Their constructions give lower bounds for particular families. In his thesis, Erskine proves the lower bound `13/36` for the limiting inferior by interpolating Vetrík’s graphs. This numerical bound is a literature comparison. The declaration `circulant_order_limit` proves convergence by interpolating arbitrary seeds. The literature check also covered later work on extremal circulants at fixed degree, including Lewis’s degree-ten and degree-eleven results, where diameter varies. [Bevan–Erskine–Lewis](https://arxiv.org/abs/1506.04962) · [Erskine, Theorem 3.7](https://oro.open.ac.uk/49440/1/Thesis_GrahameErskine.pdf) · [Lewis, degrees ten and eleven](https://www.sciencedirect.com/science/article/pii/S0012365X18301705)

All nine public theorems print only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the proofs. [Replay instructions](../README.md#replay)
