# Mean of paired Cunningham chain constants

Fix positive lengths $k$ and $\ell$. Start a first-kind chain at $n$ and a second-kind chain at $n+g$, with $g\ge2$. Write $S_{k,\ell}(g)$ for the limit of the canonical Bateman–Horn partial products of the combined $k+\ell$ linear forms. This limit exists for each gap. Its average over $2\le g\le H+1$ tends to $C_k C_\ell$ as $H\to\infty$, where $C_j$ is the single-chain constant. Both conclusions are unconditional. A gap contributes a positive constant exactly when every prime through $k+\ell$ leaves some seed residue on which all forms are nonzero. Gaps with a zero local factor stay in the average. [Canonical partial products](CunninghamPairedCountingForms.lean) · [Mean theorem](CunninghamGapAverage.lean) · [Finite positivity test](CunninghamGapAdmissibility.lean) · [Single-chain constants](BatemanHornCounts.md)

Let $N_{k,\ell}(x,g)$ count natural seeds $n\le x$ for which the two chains have **exactly** the specified lengths. Both successors must be nonprime. Assuming the pinned Bateman–Horn conjecture, for every fixed $g\ge2$,
$$
\lim_{x\to\infty}\frac{(\log x)^{k+\ell}}{x}N_{k,\ell}(x,g)=S_{k,\ell}(g).
$$
Consequently, the average of these limits tends to $C_k C_\ell$. The seed limit is taken before the average over gaps. When a prime $q$ obstructs the joint prefix, any seed producing that prefix satisfies $n\le q$, unconditionally. [Exact counts and obstructed gaps](CunninghamPairedExactMean.lean)

For example, $k=\ell=1$ counts prime pairs $n,n+g$ for which $2n+1$ and $2(n+g)-1$ are both nonprime. The mean coefficient is 1. Odd gaps have coefficient zero because one seed is even. The theorem averages over both parities.

## Proof

At a prime $q$, each ordered pair of individually allowed residues has a unique difference. Summing the joint local factor over a full period of gaps therefore gives $q$ times the product of the separate factors. The Chinese remainder theorem gives the corresponding identity for all primes below $Y$. Nonnegativity bounds the incomplete-period error in the mean by the full-period mean times $P/H$, where $P$ is the product of these primes. [Single-prime identity](CunninghamGapLocalMean.lean) · [Incomplete periods](CunninghamGapPeriod.lean)

For large primes the only extra factor comes from a shared root of the two prefixes. If the root is shared at depths $i$ and $j$, the prime divides
$$
2^{i+j}(g-2)+2^i+2^j.
$$
The product $D$ of these positive integers over all depth pairs is at most $(2^{k+\ell}g)^{k\ell}$. Beyond a sufficiently large cutoff, the logarithm of the product of the extra factors is bounded by $2(k+\ell)\log D/(Y\log Y)$. Taking $Y=\lfloor\log_{16} H\rfloor$ makes this bound tend uniformly to zero for the gaps being averaged, while $P\le4^Y$ controls the incomplete period. The two estimates pass the local identity to the full singular series. [Shared roots](CunninghamGapCollisions.lean) · [Local factor bounds](CunninghamGapWeights.lean) · [Tail estimate](CunninghamGapTail.lean)

The $k+\ell$ polynomials are distinct for the stated gaps. Their simultaneous primality predicate agrees with both canonical chain prefixes. At an admissible gap, Bateman–Horn yields the prefix-count limit. Extending either prefix by one site gives a count of lower order, so enforcing both stops preserves the coefficient. At an obstructed gap the seed bound gives the zero limit directly. The declarations are in `CunninghamChain.GapMean`. The count theorems take `type_of% BatemanHornConjecture.bateman_horn_conjecture` as an explicit hypothesis. Jones’s unconditional existence questions remain open. [Pinned Cunningham predicates](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean) · [Pinned Bateman–Horn statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Wikipedia/BatemanHornConjecture.lean) · [Jones](https://arxiv.org/abs/1104.1579)

## Sources and checks

Gallagher’s mean-value theorem concerns the singular series for prime tuples. Pintz gives a proof uniform in the size of the tuple. Kowalski’s Proposition 5.2 treats independently translated copies of one polynomial family. Here the opposite recurrences have independently specified lengths and one varying relative gap. This notebook formalizes the averaging argument for these predicates. [Pintz](https://arxiv.org/abs/1004.1084) · [Kowalski, Proposition 5.2](https://people.math.ethz.ch/~kowalski/singular-series-distribution.pdf#page=21)

An independent enumeration checked 84 one-prime averages, 147 incomplete intervals, 38,650 tests of the shared-root identity and 52,500 comparisons of exact stops with prefix extensions. Searches of DeepMind and Open Math Agents issues and PRs and 12,270 Left to Solve records found the Jones declarations and an existing single-chain termination contribution. No matching paired mean appeared. Codex assisted with the formalization. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/4755) · [Earlier statement PR](https://github.com/google-deepmind/formal-conjectures/pull/4765) · [Cunningham statement PR](https://github.com/google-deepmind/formal-conjectures/pull/4770) · [OMA termination contribution](https://github.com/lefttosolve2/open-math-agents/pull/25441) · [Left to Solve](https://lefttosolve.com/api/solved)

A fresh Lean 4.33.1 build and independent kernel replay checked 22 notebook modules. All 85 named axiom reports used only `propext`, `Classical.choice` and `Quot.sound`. The 28 named theorems in the nine new modules each have an axiom report. Run the focused notebook replay with `CunninghamGapAdmissibility`. [Replay instructions](../../README.md#replay)
