# Reflection stability at the √2 endpoint of Erdős 864

Let `A ⊆ [1,N]` have size `k`, with at most one integer that has two or more unordered representations as a sum from `A`. Diagonal pairs count. If `k/√N → √2`, deleting `o(√N)` elements leaves a set symmetric about half the exceptional sum. Consequently this endpoint is attainable along unbounded lengths **if and only if** there are Sidon sets `B ⊆ [1,L]` with `|B|/√L → 1` and `3B ∩ (B+e) = ∅` for some `e ∈ {0,1}` at each length. Here `3B` allows all triples, including repeated elements. [Lean proof](Erdos864WeightedCore.lean)

## The cost of an unpaired element

Let `c` be the exceptional sum, choosing any center if all sums are unique. Write `R = {a ∈ A : c−a ∈ A}` using integer subtraction, and put `u = |A ∖ R|`. For a positive shift `d`, two distinct pairs `(x,x+d)` and `(y,y+d)` force `x+y+d = c`: their cross sums have different unordered representations. A third starting point is therefore impossible. Give weight 1 to each point of `R` and weight `√2` to each other point. A doubly represented shift uses only points of `R`, and a singly represented shift has product of weights at most 2. The total weighted mass at each positive shift is at most 2. The difference–reflection argument and the finite symmetric-half characterization already appear in the Erdős Problem a Day working report, §§2 and 7. [Working report](https://erdosproblemaday.com/report/864)

Set `W = k + (√2−1)u`. Apply Cauchy–Schwarz to the sum of the weighted indicators of `H` consecutive translates. The diagonal contributes at most `2Hk`; each ordered pair of different translates contributes at most 2. For every integer `H ≥ 1` this gives
```text
H W² ≤ 2 (N+H)(k+H−1).
```
Choosing `H = ⌊√(Nk)⌋+1` gives the finite estimate
```text
k + (√2−1)u ≤ √2 (√N + √k).
```
If `k/√N → √2`, division by `√N` gives `u/√N → 0`. The reflected core still satisfies the original representation condition, and its normalized size tends to `√2`.

## Recovering the two halves

Write `c = 2m+e` with `e ∈ {0,1}`. Each noncentral reflection pair is uniquely `{m+x, m+e−x}` with `1 ≤ x ≤ ⌊N/2⌋`. The offsets form a Sidon set `B`: equality of two upper-half sums forces equality of their unordered pairs. A collision between an upper-half sum and a mixed sum is equivalent to `a+b+d = x+e` with all four variables in `B`. Reflection accounts for lower-half sums. Thus `3B ∩ (B+e) = ∅` and `2|B| ≤ |R| ≤ 2|B|+1`, allowing the fixed point when `c` is even.

Conversely take any such `B ⊆ [1,L]` and choose `m=L+1`. Its two reflected copies lie in `[1,2L+1]`, are disjoint and give exactly `2|B|` labels. The Sidon and avoidance conditions make every sum outside `2m+e` unique. These finite constructions in both directions yield `endpoint_iff_admissible`.

The file uses the pinned `Erdos864.HasAtMostOneRepeatedSum` and `IsSidon` directly. Its endpoint is the weaker upper constant `√2`. Erdős and Freud obtained the lower constant `2/√3`; the matching conjectured upper bound remains open. All eight public theorems print only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the formalization. [Pinned problem](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/864.lean) · [Pinned Sidon predicate](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjecturesForMathlib/Combinatorics/Basic.lean) · [Erdős–Freud](https://doi.org/10.1016/0022-314X(91)90083-N) · [Replay instructions](../README.md#replay)
