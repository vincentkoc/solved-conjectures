# Green 28 with two positive mass values per marginal

Let $P,Q$ be independent integer laws. Suppose their sum is uniform on its finite support and each marginal takes at most two distinct **positive probability values**. Then both marginals are uniform if either of the following holds.

- One marginal has at most four atoms. The other can have arbitrarily many atoms.
- The two support sizes are equal to the same prime, of any size.

The positions of all atoms and the actual probabilities are unrestricted. The two-level hypothesis is imposed on both laws. The general integer problem with an arbitrary four-site marginal remains open. The formal statements use the pinned `Green28.indepSum` and `Green28.IsUniformOnSupport`. Uniformity of the sum already supplies the two marginal finite-support hypotheses of the pinned conjecture. [`uniform_of_one_small_support` and `uniform_of_equal_prime_sizes`](Green28TwoMassLevels.lean) · [Pinned statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean)

## What a counterexample would require

Normalize each marginal by its own largest mass. After interchanging the laws if necessary, the normalized positive weights would be $1,u$ on the left and $1,1-u$ on the right. Partition the respective supports into high and low classes $G,H$ and $K,L$. For some integer $m\ge2$,
\[
 u^2-(m+1)u+1=0,\qquad |H||K|=|G||L|+m|H||L|.
\]
In particular the smaller weight is the smaller root of this quadratic and is at most $(3-\sqrt5)/2$. The fractions of high sites relative to low sites satisfy $|K|/|L|-|G|/|H|=m$. These conditions are necessary. No counterexample is constructed. [`two_level_alternative` and `Pattern`](Green28TwoMassLevels.lean)

Each occupied sum has exactly one of the following three representation counts. An unoccupied site has four zero counts. The counts distinguish the left and right marginals.

| Sum type | High–high | High–low | Low–high | Low–low |
| --- | ---: | ---: | ---: | ---: |
| Single high–high pair | 1 | 0 | 0 | 0 |
| Two mixed pairs | 0 | 1 | 1 | 0 |
| Low–low pair with mixed partners | 0 | 0 | $m$ | 1 |

To see this, the rightmost sites of each marginal attain maximal mass. Their sum is unique and fixes the normalized output mass at one. At the greatest sum involving a low site, there can be no low–low pair and at most one mixed pair from each orientation. A single mixed contribution is strictly between zero and one, so both occur and the low weights add to one. At the greatest low–low sum, that pair is unique among low–low pairs. Mixed contributions from both orientations would already total at least one. Thus all remaining contributions are of one orientation, giving $mu+u(1-u)=1$. This forces $m\ge2$. At an arbitrary sum, replace $u(1-u)$ by $1-mu$. The constant and the coefficient of $u$ are integers. Since $u$ is irrational, its coefficient must vanish and the constant is zero or one. This gives the table. [`fiber_counts`](Green28TwoMassLevels.lean) · [Irrationality of nonmaximal normalized weights](GREEN-28-ARITHMETIC.md)

For any $h\in H$ and $l\in L$, the $m$ mixed partners of $h+l$ all use other low rows. Thus $|H|\ge m+1$. At the greatest low–low sum their high columns lie strictly above $\max L$, and at the least such sum they lie strictly below $\min L$. Hence $|K|\ge2m$. The two end sites of each nonuniform law both have maximal mass. Consequently $|G|+|H|\ge5$ and $|K|+|L|\ge5$, proving the first result. For a common prime size $p$, the count identity gives $p|H|=p|L|+m|H||L|$. The positive low counts are strictly smaller than $p$, so $p$ divides $m$. The same count identity gives $m\le|K|<p$, a contradiction. [Support and prime-count proofs](Green28TwoMassLevels.lean)

## Sources and verification

Hare's trinary coefficient method distinguishes zero, one and intermediate weights. Hasanbegović's Lemmas 2–3 analyze the first aligned nonbinary coefficients. The proof here uses the two actual mass values, the opposite endpoint of the low–low sums, and the integral arithmetic of normalized probabilities to obtain the quadratic and the per-sum counts. The earlier four-atom result permits arbitrary weights but bounds both support sizes. Searches of DeepMind and Open Math Agents for the two-level or equal-prime statements found no matching implementation. Left to Solve lists no solution of the general problem. [Hare](https://arxiv.org/abs/2307.07363) · [Hasanbegović, §2](https://arxiv.org/html/2611.14596v1) · [Earlier four-by-four theorem](GREEN-28-FOUR-ATOMS.md) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Open Math Agents degree and reflection reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/21793) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28)

The verification rebuilds the pinned source and all four local modules from clean sources with Lean 4.33.1, then independently replays each local module with the kernel checker. All four axiom reports in the new file contain only `propext`, `Classical.choice` and `Quot.sound`.
