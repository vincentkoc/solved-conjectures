# Green 33 · Weighted sum peaks

Let $P,Q$ be independent laws on a common seed $A\subseteq\mathbb Z/M$, and let $R$ be the law of their sum. Write $U$ for uniform on the cyclic group, $\delta=d_{\rm TV}(R,U)$, and $H=M\max_z R(z)$ for the largest output probability in units of uniform mass.

If $M\to\infty$, $\delta\to0$, and $|A|\le(c+o(1))\sqrt M$ for a fixed $0<c<2$, then **$H\to\infty$**. More precisely, put $D=M\sum_z(R(z)-1/M)^2$, the Pearson chi-squared divergence. The finite bound $D\le\delta H$ and the lower limits are
\[
\liminf D\ \ge\ \frac{(1-c^2/4)^4}{c^2},\qquad
\liminf D\ \ge\ \tfrac12\quad\text{at }c=\sqrt2 .
\]
Both bounds therefore hold for $\liminf\delta H$. The second applies to every witness of the weighted reformulation of Green 33. It constrains the concentration that any such family must exhibit. Its existence remains open. [Rate, divergence and critical-budget theorems](Green33WeightedPeaks.lean) · [Weighted equivalence](WEIGHTED-STABILITY.md) · [Pinned conjecture](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

## Why a peak is forced

Set $n=|A|$, $b=\sum_i\min(p_i,q_i)$ and $s=\sum_i p_iq_i$, where $p_i,q_i$ are the input masses. Cauchy–Schwarz gives $b^2\le ns$. Partition the labels into $T=\{i:p_i\ge q_i\}$ and its complement. The probability of drawing the first label in $T$ and the second in $T^c$ is at least $1-b$. Those draws give at most $|T||T^c|\le n^2/4$ different sums. Comparing this event with $U$ gives
\[
 b\ge 1-\delta-\frac{n^2}{4M}.
\]
At the Green budget the earlier marginal stability theorem gives the stronger fact $b\to1$ by testing both laws on $T$. [Overlap count](Green33WeightedPeaks.lean) · [Marginal stability](Green33WeightedStability.lean)

The sum and difference laws have the same collision probability. Exchange the second draws in two independent pairs to pass between equal sums and equal differences. This weighted version of the additive-energy identity holds in any finite abelian group. The difference law has mass $s$ at zero for injectively labelled seeds. Its centered square there is bounded by the sum of all centered squares, hence
\[
 s\le \frac1M+\sqrt{D/M}.
\]
Together the two estimates imply $\sqrt D\ge b^2/(n/\sqrt M)-1/\sqrt M$. For the upper bound on $D$, summing $R(z)(R(z)-1/M)$ over all residues gives $D/M$. The residues with positive excess contribute at most $\max_z R(z)$ times the total positive excess, which equals $\delta$. The earlier unweighted notebook compares ordered representation counts using the same exchange. [Weighted energy proof](Green33WeightedPeaks.lean) · [Unweighted multiplicity bound](NOTES.md)

## Exact uniformity and the cutoff at two

In any finite abelian group of order $M$, an **exactly uniform** independent sum requires at least $2\sqrt M-1$ labels in the union of the two supports. Indeed $s=1/M$ by the energy identity. Every individual cell has $p_iq_j\le1/M$. Take $a=\max_i p_i$ and $d=1/(Ma)$, so every $q_i\le d$. Summing $(a-p_i)(d-q_i)\ge0$ gives $n/M\ge a+d-1/M$. Since $ad=1/M$, the arithmetic–geometric mean inequality gives the claim. Exact modular deconvolution was studied by Sherstnev. The finite support-budget estimate here follows directly from the collision probabilities. [`exact_uniform_budget`](Green33WeightedPeaks.lean) · [Sherstnev, *A Random Variable Uniformly Distributed on a Finite Abelian Group as Sum of Independent Summands*](https://doi.org/10.1137/S0040585X97976957)

The bound is attained for every square cyclic order $M=k^2$. The independent fair digits range over $\{0,\ldots,k-1\}$ and $\{0,k,\ldots,(k-1)k\}$, which share only zero and represent every residue once. At **every** positive order, use $k=\lfloor\sqrt M\rfloor$ and the same digits. Their sum is uniform on $[0,k^2)$ inside the cyclic group. It uses at most $2k-1$ labels, with TV error at most $1-k^2/M$ and normalized peak at most $M/k^2$. These bounds tend to zero and one, respectively, as $M\to\infty$. Thus coefficient two is attained for near-uniform sums with bounded peaks at all orders. [Radix construction and every-order bounds](Green33WeightedPeaks.lean)

The source comparison uses the pinned Green 33 predicate and the previously checked equivalence to independent weighted draws. The DeepMind issue and formalization PR, Left to Solve, Open Math Agents, and the personal notebook were checked for matching weighted peak and support estimates. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Formalization PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents/issues?q=%22Green33%22)

A clean Lean 4.33.1 build and independent kernel replay covered all six notebook modules. All 56 axiom reports contain only `propext`, `Classical.choice` and `Quot.sound`. Replay `Green33WeightedPeaks` with the [notebook runner](../../scripts/replay-research).
