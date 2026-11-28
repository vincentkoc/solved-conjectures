# Green 28 for a uniform sum on at most ten sites

If the sum of two independent integer laws is uniform on a set $S$ of at most ten integers, **each original law is uniform on its own support**. The gaps in $S$ can be arbitrarily large. Uniformity of the sum already makes both input supports finite, as required in the pinned question. [`uniform_of_ten_outputs`](Green28OutputCardinality.lean) · [Pinned Green 28](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean)

## Counting the output values

Write $A,B$ for the marginal supports. Let $h,k$ count the sites of maximal mass in each law, respectively. In any counterexample $h,k\ge2$ and
\[
 |S|\ \ge\ hk+\max\{|B|+h-1,\ |A|+k-1\}.
\]
In particular $|S|\ge\max(|A|,|B|)+5$. If $|S|\le10$, this would put both marginals within the earlier theorem for at most five atoms per side. [Count for the original PMFs](Green28OutputCardinality.lean) · [Five-site theorem](GREEN-28-ISOLATED-TABLES.md)

Translate both supports so that their minima are zero. Their endpoints have maximal mass. An ordered pair gives a uniquely represented sum exactly when both its sites have maximal mass. Hence maximal pairs give $hk$ distinct singleton sums. In a counterexample the first sites of deficient mass in the two supports have the same offset $r$. Thus each of the $|B|$ totals in $r+B$ has multiple representations. For every nonzero maximal site $x$ of the first support, $x+r$ also has multiple representations. It lies outside $r+B$, since otherwise $x$ would belong to $B$ and the maximal pair $(x,0)$ would collide with $(0,x)$. These $h-1$ further totals are distinct. Interchanging the laws proves the other count. [Aligned deficient sites and the maximal-pair criterion](Green28UnpairedSites.lean) · [Finite-set counting lemma](Green28OutputCardinality.lean)

The theorem also applies to larger output sets whenever their cardinality exceeds that of the larger marginal by at most four. For example, ten-site sums need not be consecutive or come from a constant summand. Uniform laws on $\{0,1\}$ and $\{0,10,100,1000,10000\}$ realize such a sum. Every independent decomposition of the same uniform sum law satisfies the conclusion.

## Scope and verification

Hare studies the distinction between zero, maximal and deficient coefficients in binary products. Hasanbegović aligns the first nonbinary coefficients. The bound here counts output **values**, with unrestricted degrees and spacings. The unrestricted conjecture remains open. The ten-site threshold follows from this count and the five-site theorem. [Hare](https://arxiv.org/abs/2307.07363) · [Hasanbegović, §2](https://arxiv.org/html/2611.14596v1)

The live search covered DeepMind's issue and statement PR, Left to Solve, OMA's two located reductions and the personal notebook. Lean 4.33.1 rebuilt the pinned declaration and eight notebook modules from source. Each notebook module passed independent kernel replay. The 34 axiom reports list exactly `propext`, `Classical.choice` and `Quot.sound`. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28) · [OMA first reduction](https://github.com/lefttosolve2/open-math-agents/pull/9606) · [OMA polynomial reduction](https://github.com/lefttosolve2/open-math-agents/pull/21793)
