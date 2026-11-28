# Reflected Sidon layers miss one eighth and are expensive to extend

Let `p` tend to infinity through primes, `k=p−1`, and `m=p(p−1)`. Put Ruzsa’s cyclic Sidon set `B` in the even subgroup of `ℤ/(2m)`, and reflect it about any odd residue `j` to form `A=2B ∪ (j−2B)`. Then `|A|=2k`, so `|A|/√(2m) → √2`, but the fraction of residues missing from `A+A` tends to **1/8**. The center may change at each prime. Every two-basis containing these labels has eventual normalized size above each constant below **`(3+√3)/(2√2) ≈ 1.6730`**. This exceeds the attained constant `√(18/7) ≈ 1.6036` for unrestricted ordinary cyclic bases. [Overlap proof](Green33ReflectedLayers.lean) · [Repair proof](Green33SidonLayerRepairs.lean) · [Existing cyclic construction](STRICT-COVER-LIFT.md)

For arbitrary nonempty cyclic Sidon seeds of size `k∼√m`, a related statement holds for almost every reflection parameter. Write `S=B+B` and `I(c)=|S ∩ (c−S)|`. For every fixed `δ>0`, the proportion of residues `c` with `|4I(c)−m| ≥ δm` tends to zero. Exceptional parameters can remain for general seeds. [Lean declaration `typical_centers`](Green33ReflectedLayers.lean)

## Counting the two layers

In half-order coordinates the even sums are `S ∪ (c−S)`, where `2c=2j` in the doubled group under the even embedding. The odd sums are a translate of `B−B`. Sidonicity gives `2|S|=k²+k` and `|B−B|=k²−k+1`. The full sumset therefore has exactly `2k²+1−I(c)` residues. For Ruzsa’s `m=k(k+1)`, the number of holes is `2k−1+I(c)`.

Let `Pᵣ(c)` count ordered `r`-tuples from the seed with sum `c`. Every represented two-sum has two ordered representations except a diagonal sum, which has one. All diagonal sums are distinct. Expanding the product of the counts at `x` and `c−x` gives `0 ≤ 4I(c)−P₄(c) ≤ 4k`.

## Why the count concentrates

Let `d(t)` be the ordered difference count. Write `D=Σₜ |d(t)−1|`; for a nonempty Sidon seed this is exactly `m−k²+2k−2`. The operator `Tf(x)=Σ_{b∈B} f(x−b)` satisfies `Σ(Tf)² ≤ D Σf²` on mean-zero real functions. To see this, group the square by differences. The constant part vanishes, and each translated inner product has absolute value at most `Σf²`. Iteration controls the variance of `Pᵣ` by `Dʳ`. Starting at `r=2` with the sharper variance bound `2k²` yields the finite estimate
```text
Σc (4I(c)−k⁴/m)² ≤ 4k²D² + 32mk².
```
When `k∼√m`, dividing by `m³` proves the concentration statement. For `D=O(k)`, only a bounded number of parameters can deviate from quarter overlap by any fixed positive fraction of the modulus. Relative to an actual odd center `j=1+2t`, the parameter is `c=1+2t mod m`, with at most two shifts per parameter. [Sidon incidence estimates in finite fields, Cilleruelo](https://arxiv.org/abs/1003.3576)

For Ruzsa’s graph the points are `(a,a)` with `a∈𝔽ₚˣ`, with multiplication in the first coordinate and addition in the second. Scaling every entry of an `r`-tuple by a unit `u` preserves its multiplicity and sends its target `(x,y)` to `(uʳx,uy)`. At most `r` scalars have any one image, even at `y=0`. The variance bound gives a pointwise estimate over every finite field of order `k+1`:
```text
k (Pᵣ(x,y)−kʳ/m)² ≤ r (3k−2)ʳ,     m=k(k+1), r≥1.
```
In the prime case, if `H=2m−|A+A|`, the resulting cyclic certificate is `|4H−m| ≤ 18k√k+12k`. For a containing basis of size `b`, each missing residue requires a new unordered pair. Thus `2H+|A|²+|A| ≤ b²+b`, which gives the lower constant `3/2`. [Ruzsa’s cyclic construction and Sidon proof](SIDON-QUOTIENT-PROFILE.md) · [Caicedo, Gómez, Gómez and Trujillo on modular Sidon constructions](https://arxiv.org/abs/1411.5741)

## Counting which added pairs can help

Write `u=|U|` for labels added in one coordinate layer and `h=m−|B−B|` for the seed’s missing differences. For each new label `x`, counting triples in `B` gives `Σ_b r_{B+B}(x+b) = Σ_a r_{B−B}(x−a)`. Each represented difference contributes at least one on the right; a represented sum contributes at most two on the left. Consequently
```text
2 |(U+B) ∖ (B+B)| ≤ ku + e,      e² ≤ h(ku+u²).
```
Here `e` counts the pairs in `U × B` whose difference is missing from `B−B`. Cauchy–Schwarz gives the squared bound: for fixed distinct labels of `U`, at most one pair of seed elements has the required difference, and equal labels contribute `uk` in total.

Let `w` be the total number of new labels across both layers. At most `h` missing odd residues can be repaired. Mixed pairs with one new and one old label can repair an even residue only within its own parity layer. Pairs of two new labels cover at most `w(w+1)/2` additional residues. The resulting finite certificate for the original hole count `H` is
```text
2H ≤ 2h + kw + 2e + w²+w,       e² ≤ h(kw+w²).
```
When `k/√m → 1` and `I(c)/m → 1/4`, one has `H/m → 1/4` and `h/m → 0`. Along any subsequence with bounded `w/√m`, the certificate forces every limit point `d` of that ratio to satisfy `d²+d ≥ 1/2`. Thus at least `((√3−1)/2−o(1))√m` new labels are needed. Adding the original `2k` and dividing by `√(2m)` gives the claimed constant. The argument applies to any dense Sidon seeds whose chosen parameters have quarter overlap, and to every choice of reflections for Ruzsa’s graph.

## Scope

Green 33 asks for an unbounded sequence of ordinary cyclic two-bases with normalized size tending to `√2`. The file uses the same `Finset (ZMod q)`, `A+A=univ` convention with diagonal pairs, and the pinned `IsSidon` predicate. It rules out one construction and its sublinear repairs. The earlier quarter-hole theorem concerns projection onto a quotient of half the order. Guo, Lin and Tang give a sharper arithmetic estimate for tuples with prescribed product and nonzero prescribed trace. The elementary graph estimate also covers additive coordinate zero. No priority claim is made for the arithmetic estimates. [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Pinned Sidon predicate](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjecturesForMathlib/Combinatorics/Basic.lean) · [Guo–Lin–Tang](https://arxiv.org/abs/2607.23275)

All sixteen public theorems across the two modules print only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the formalization. [Replay instructions](../README.md#replay)
