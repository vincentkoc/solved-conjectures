# Which laws attain the square-order common support bound?

Let $G$ be a finite abelian group of order $k^2$. Two independent probability laws on a common list of $2k-1$ labels have an exactly uniform sum if and only if their masses have the following form, after possibly exchanging the laws. The labels may initially repeat. Equality forces distinct labels. [Classification and proof](Green33SquareTilings.lean) · [Common support lower bound](WEIGHTED-SUM-PEAKS.md)

* The first law is uniform on a set $B$ of $k$ labels.
* The second law assigns $1/k$ to each of the $k-1$ labels in $C=A\setminus B$. Its remaining mass $1/k$ can split over $B$.
* For each $t\in B$ receiving positive mass from the second law, addition takes $B\times(C\cup\{t\})$ bijectively onto $G$.

Thus the second law is a convex combination of the fair laws on $C\cup\{t\}$. The coefficient of a completion at $t$ is $k$ times the second law's mass at $t$. The converse holds for every choice of these coefficients. In particular a seed of minimum size admits an exact real factorization precisely when it contains two $k$-sets giving a direct tiling. [Theorems `TilingMixture.weights`, `flat_iff_tiling_mixture` and `exists_flat_iff_tiles`](Green33SquareTilings.lean)

Once a single $t$ works, another $u\in B$ works exactly when $B+u=B+t$. The possible inside labels form the intersection of $B$ with one coset of the translation stabilizer of $B$. If the translates are distinct, both input laws are fair. With a periodic tile the freedom is real. In $\mathbb Z/4$, take the first law uniform on $\{0,2\}$. The second can put $1/2$ on $1$ and split the remaining $1/2$ arbitrarily between $0$ and $2$. Each sum then has probability $1/4$. [Completion and aperiodicity theorems](Green33SquareTilings.lean)

## Why equality forces a tiling

Scale the two probability vectors by $k$, writing them as $f,g$. Each has total mass $k$. The atom caps from the common-support bound give $f\le a$ and $g\le b$ with $ab=1$, and the diagonal collision bound gives $\sum_i f_i g_i\le1$. Summing $(a-f_i)(b-g_i)\ge0$ over $2k-1$ labels gives $a+b\le2$. Hence $a=b=1$, and at each label at least one vector equals one. One vector must attain one at $k$ labels, since two sets of size at most $k-1$ cannot cover $2k-1$ labels. This exhausts that vector's entire mass. [Atom caps](Green33WeightedPeaks.lean) · [Equality argument](Green33SquareTilings.lean)

In a fixed sum fibre the products of the scaled masses add to one. A pair from $B\times C$ contributes one and exhausts that fibre. For any positive residual atom $t$, the extra pairs from $B\times\{t\}$ therefore avoid all those sums. Together the $k^2$ pairs have distinct sums and tile $G$. Sherstnev characterized uniform convolution decompositions on finite groups. The notebook gives an equality classification for a minimum common label budget, including an explicit description of the allowed mixtures. [Sherstnev](https://doi.org/10.1137/S0040585X97979937)

## Scope and replay

The pinned Green 33 declaration asks for ordinary two-bases at size $(\sqrt2+o(1))\sqrt{|G|}$ along infinitely many cyclic orders. The present result concerns exact uniformity at the larger budget $2\sqrt{|G|}-1$ on square-order groups. The link to Green 33 comes through the notebook's separate equivalence using approximate uniformity. [Canonical statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Weighted equivalence](WEIGHTED-STABILITY.md)

The source issue closed with the statement formalization. The Left to Solve entry had no solution. Searches in DeepMind, Open Math Agents and the personal notebook found no matching square-order classification. [Source issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents/issues?q=%22tiling+complement%22+%22uniform%22)

Replay **Green33SquareTilings** using the [notebook runner](../../scripts/replay-research). Seven notebook modules underwent fresh compilation and independent Lean 4.33.1 kernel replay. All 65 printed axiom sets are subsets of the standard three.
