# Green 28 with three positive partner masses

Let $P,Q$ be integer laws whose independent sum is uniform on its support. Suppose $P$ takes at most three distinct positive probability values, and at most one atom of $Q$ has less than maximum mass. **Both marginals are uniform if $Q$ has at most four atoms.** More generally, it suffices that at most one occupied site lies strictly to the left or strictly to the right of its possible deficient atom. The support of $P$ can be arbitrarily large. Both claims use the integer laws and independent sum from the pinned problem. [Lean statements](Green28ThreeLevelPartner.lean) · [DeepMind Green 28](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean)

## The remaining possible weights

Normalize each law by its own largest probability. In any nonuniform example, $Q$ has a unique deficient atom at $d$ with weight $u$. Write $x=1-u$. Then $P$ has exactly three weights $1,x,y$. For some integer $k\ge2$,
\[
  x^2-(k+1)x+1=0,\qquad
  y=1-kx\quad\text{or}\quad (k=2\ \text{and}\ y=1-x).
\]
The root is determined by $0<x<1$. At least $k$ occupied sites of $Q$ lie **on each side** of $d$. Also $u^2+u=1+(k-2)x\ge1$, so any $u<(\sqrt5-1)/2$ forces uniformity irrespective of support geometry. These are necessary conditions on a counterexample. Existence for any listed weight is open. [`three_level_data`, `flank_sizes` and `uniform_of_small_exception`](Green28ThreeLevelPartner.lean)

## Reading the fibres

For any occupied row $i$ of normalized weight $w_i$, its contribution to the sum $i+d$ is $uw_i$. The other contributions are the normalized weights of distinct deficient rows, each paired with a maximum-weight column. They sum to $1-uw_i$. At the leftmost row, all these other rows lie at or above the first deficient row. The alignment of the first deficient offsets places them at or below that same row. Consequently there is exactly one such site and its weight is $x=1-u$. [Complementary remainder](Green28DeficientFibre.lean) · [Alignment of the first deficient sites](Green28UnpairedSites.lean)

A fibre supported entirely on deficient rows gives $mx+ny=1$ for counts $m,n$. Each normalized deficient weight is irrational, so this requires a second distinct weight $y$ and both counts are positive. The three-value hypothesis accounts for all occupied weights. Fibres through a row of each deficient type give further counts
\[
 ux+ax+by=1,\qquad uy+cx+ey=1.
\]
The counts may differ between fibres. The argument below applies to **every** choice of the $x$-row, with a fixed $y$-row and boundary fibre. [Deficient fibre and integer span](GREEN-28-DEFICIENT-FIBRE.md)

## The integer calculation

Multiplication by $x=1-u$ on the integer span of $x,y$ is given by an integer matrix. Its rows follow by subtracting the three displayed fibre equations. The degree-two matrix identity gives $x^2=Tx+K$ for integers $T,K$. Hence each element of $\mathbb Z[u]$ is an integer linear combination of $1,x$. Since $y$ belongs to this order, write $y=s+tx$ with integral $s,t$. Comparing rational coefficients of $1,x$ in $mx+ny=1$ gives $ns=1$, hence $n=1$ and $y=1-mx$. [Formal integer-coordinate argument](Green28ThreeLevelPartner.lean)

Substitution in the $x$-row equation gives $x^2=(1+a-bm)x+b-1$. Comparing constants in the $y$-row equation gives $m(b-1)+e=0$. Thus $b\le1$, and $b=1$ would make the positive $x$ rational. It follows that $b=0$, $x^2-(a+1)x+1=0$, and $a\ge2$. Comparing the linear coefficients yields $m(a-m)\le1$. The positivity of $y=1-mx$ and the quadratic relation imply $m\le a$. Thus $m=a$ or $(m,a)=(1,2)$. The polynomial relation fixes the same $a=k$ at every $x$-row. [`count_classification`](Green28ThreeLevelPartner.lean)

In the fibre $i+d$ of an $x$-row there must therefore be $k$ other rows of weight $x$ and no row of weight $y$. Take the leftmost such $i$. Every other row $j$ lies strictly to its right and gives a distinct column $i+d-j<d$. The rightmost $x$-row gives $k$ distinct columns above $d$ by the same calculation. Including $d$ requires at least $2k+1$ sites. [Flank counts and four-site criterion](Green28ThreeLevelPartner.lean)

## Scope and sources

The earlier two-value theorem obtains a quadratic unit when **both** laws have at most two mass values. The present proof allows a third opposite mass and uses the single deficient site to determine that third value, the exceptional ratio, and the site counts. The trinomial manuscript treats one factor with three terms and an unrestricted partner. The four-site result above retains the stated mass assumptions and permits an unbounded opposite support. Green 28 in full remains open. [Two-value theorem](GREEN-28-TWO-MASS-LEVELS.md) · [Ghidelli](https://arxiv.org/abs/2209.09843) · [Hare](https://arxiv.org/abs/2307.07363) · [Hasanbegović](https://arxiv.org/html/2611.14596v1) · [Trinomial manuscript](https://hexagonmath.org/pdf/2611.00674v2)

The live DeepMind issue and statement PR, Left to Solve and both OMA reductions were checked. The searches found no matching three-weight classification with arbitrary support widths. Lean 4.33.1 rebuilt the pinned declaration and eight notebook modules from clean sources. Independent kernel replay passed for all eight, and all 51 axiom reports contained exactly `propext`, `Classical.choice` and `Quot.sound`. For replay use `Green28ThreeLevelPartner` with the notebook runner in the pinned Lake environment. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28) · [First OMA reduction](https://github.com/lefttosolve2/open-math-agents/pull/9606) · [Second OMA reduction](https://github.com/lefttosolve2/open-math-agents/pull/21793) · [Replay runner](../../scripts/replay-research)
