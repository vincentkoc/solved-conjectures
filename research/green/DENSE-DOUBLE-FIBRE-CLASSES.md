# Affine classes of dense doubles with larger fibres

Let $s\ge5$, $r\ge0$, $g=2s+3$ and $n=g-1+r$. Consider $S=A+A\subseteq\mathbb F_2^n$, where $A$ has density greater than $\tfrac12-\binom{2s}{s}/2^{2s+1}$ and the largest affine subspace inside $S$ has dimension $n-2$. Write $k=|S^c|$. Assume
$$
\min(5g+12,4g+20)\,2^r<8k.
$$

Fix a spanning odd circuit with $g$ points in $\mathbb F_2^{g-1}$. Each missing set has a presentation by $g$ nonempty subsets of $\mathbb F_2^r$, one over each circuit point. Conversely, every such family with $k$ points in total gives the missing set of a double satisfying the original conditions. [Presentations and realization](Green51FibrePresentations.lean)

Two doubles are affinely equivalent precisely when a single $u\in\mathrm{GL}(r,2)$ makes the following counts agree. For each translation class of subsets of $\mathbb F_2^r$, count the rows in that class after applying $u$ to the first family, and compare with the count in the second family. Thus rows can be permuted and translated independently, while the same linear transformation acts on every row. This applies to all fibre dimensions, including zero. [Classification of the original sumsets](Green51DenseFibreClassification.lean)

### Why the ambient affine group gives this test

For a row mask $D$ of size $k$, compare $D$ with $D+t$. A translation along the fibre keeps both sets in a carrier of size $g2^r$, so their intersection has at least $2k-g2^r$ points. A translation across fibres can match at most two circuit rows, so the intersection has at most $2^{r+1}$ points. The size hypothesis separates these values and recovers the fibre direction from $D$. Conversely, each circuit permutation extends linearly, and the unique odd dependence on its points lets one extend independent translations of the rows to an ambient affine map. [Recognition and extension](Green51ArbitraryFibreEquivalence.lean) · [Coordinates](Green51CircuitProductChart.lean)

### Eight-point fibres

In dimension 17 take $s=6$, $r=3$ and $g=15$. The range is $81\le k\le120$, with $|A|>50{,}752$. The 255 nonempty subsets of an eight-point fibre form 45 translation classes. Listed by subset cardinality from one to eight, their counts are $1,7,7,14,7,7,1,1$.

As an independent computation, write $h=120-k$ for the unused places. For $h=0,\ldots,10$ the respective numbers of affine classes are
$$
1,\ 1,\ 2,\ 3,\ 7,\ 10,\ 21,\ 33,\ 65,\ 104,\ 195.
$$
Two finite enumerations agree on all eleven values. One lists multisets of translated row types and takes the least representative under the 168 invertible binary matrices. The other uses Burnside's lemma. For a cycle of length $j$ on translation classes of rows of size $w$, use the factor $(1-x^jy^{jw})^{-1}$. Average the coefficient of $x^{15}y^k$ over the matrices. The numerical examples are computed separately from the Lean proof of the classification. The [four-point calculation](STABLE-AFFINE-CLASS-COUNTS.md) also has a Lean proof of its numerical table.

The odd-circuit bound is due to Geelen. Alon and Zamir study the number of binary sumsets without these density and affine-dimension restrictions. Green's general guaranteed-dimension question remains open. [Geelen](https://arxiv.org/abs/1401.5769) · [Alon–Zamir](https://arxiv.org/abs/2403.16589) · [Pinned Green 51](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

From the pinned Formal Conjectures checkout, run `lake env python3 "$runner" Green51DenseFibreClassification` using the [notebook replay setup](../README.md#replay).
