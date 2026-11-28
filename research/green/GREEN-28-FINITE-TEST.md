# Green 28 with a fixed number of sum outcomes

If an independent sum of integer laws has at most $k$ possible values, put $B=5^{k+1}$. There is a relabelling of the two supports and the sum support into $[0,B]$ that preserves every atom's probability and every pair's sum under the output relabelling. The statement holds for unequal output probabilities, too. In particular, any counterexample to Green 28 with $k$ sum outcomes has one with the same masses in this bounded interval. [Weighted relabelling](Green28FiniteSearch.lean)

## The finite test

For each nonempty subset $S$ of $\{0,\ldots,B\}$ with $|S|\le k$, take two nonnegative real vectors $u,v$ indexed by $0,\ldots,B$, each summing to one. For every integer $0\le z\le 2B$ impose

$$\sum_{i+j=z} u_i v_j = \begin{cases}1/|S| & z\in S,\\0 & z\notin S.\end{cases}$$

The test asks whether each vector must equal the uniform vector on a nonempty subset of $[0,B]$. For fixed $k$, the index sets and subset choices are finite. There are $2(B+1)$ real variables and $2B+1$ convolution equations per output support. A violation is a finite real feasibility problem with rational coefficients and degree at most two. The Lean proof establishes the equivalence, and leaves the systems to be solved. The cutoff is exponential. [Definition and equivalences](Green28QuadraticTest.lean)

`Green28QuadraticTest.atMost_iff_quadraticTest` gives the equivalence at every fixed outcome budget, independently of the original diameter. `green_28_iff_quadraticTests` uses `type_of% Green28.green_28` on its left and quantifies over all budgets on its right. Uniformity and independence use the pinned PMF definitions. Uniformity of the sum already implies finiteness of the marginals. [Pinned declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean) · [Finiteness lemma](Green28UniformSums.lean)

## Proof of the cutoff

Translate $n$ labelled sites into $[0,D]$. If $D>5^{n+1}$, apply the pigeonhole principle to the fractional parts of $t a_i/D$ for $0\le t\le 5^n$, dividing each coordinate into five intervals. Two values of $t$ fall in the same box, so there are an integer $1\le q\le 5^n$ and integers $u_i$ with $|q a_i/D-u_i|<1/5$. Replace $a_i$ by $a_i-u_i$. Each new site differs by less than $1/5$ from $(1-q/D)a_i$. The slope exceeds $4/5$, while a comparison between two pair sums incurs error less than $4/5$. Integrality preserves ties as well as strict inequalities. The new interval ends at $D-q$. Induction on $D$ gives the cutoff. [Integer compression](Green28SupportCompression.lean)

Apply this construction to the **output** sites. Write their minimum as $m=x_0+y_0$, and call their new labels $F(z)$. Give an original left atom $x$ the label $F(x+y_0)-F(m)$ and a right atom $y$ the label $F(x_0+y)$. The original identity $(x+y_0)+(x_0+y)=(x+y)+m$ ensures the new labels add to $F(x+y)$. Order preservation gives nonnegativity, bounds and injectivity. Pushing the two laws forward therefore carries every weighted sum to its new site. [Convolution and mass preservation](Green28FiniteSearch.lean)

## Related work and verification

Nathanson studies compression of integer sumsets and bounds the interval needed to realize their cardinalities. The Freiman small-model principle also appears in the literature on iterated sumsets. Here the order of pair sums is retained, and separate injective maps carry the actual probabilities into a bounded instance of Green's predicate. [Nathanson](https://arxiv.org/abs/2505.20998) · [Small-model discussion after Lemma 8](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v33i1p56/pdf)

The polynomial formulation and its equivalence to the probability question are established work. Hare and Zhang discuss finite-degree computations and coefficient systems. Their degree bounds and the number of occupied sum outcomes are different parameters. Open Math Agents already formalized the polynomial/PMF equivalence and has other reductions. The original DeepMind issue closed with the statement PR. Searches of the DeepMind and Open Math Agents trackers found no matching fixed-outcome cutoff. Left to Solve lists the original as open. [MathOverflow discussion](https://mathoverflow.net/questions/339137/) · [Hare](https://arxiv.org/abs/2307.07363) · [Existing formal equivalence](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/504) · [Related Green reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/21793) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28)

Five local modules in the import closure were built from clean sources and replayed separately with Lean 4.33.1's kernel checker. All ten printed theorems in the three new modules use only `propext`, `Classical.choice` and `Quot.sound`. The original conjecture remains open.
