# Mean-square uniform sums at coefficient two

Fix cyclic orders $M_i\to\infty$ and nonempty sets $A_i\subseteq\mathbb Z/M_i$ with $|A_i|\le(2+o(1))\sqrt{M_i}$. The following conditions are equivalent for this prescribed sequence of sets.

1. There are independent laws $P_i,Q_i$ on $A_i$ whose sum law $R_i$ has vanishing Pearson divergence from uniform, meaning $D_i=M_i\sum_z(R_i(z)-1/M_i)^2\to0$.
2. There are disjoint $S_i,T_i\subseteq A_i$, each of size $(1+o(1))\sqrt{M_i}$, such that the ordinary counts $c_i(z)=|\{(s,t)\in S_i\times T_i:s+t=z\}|$ satisfy $M_i^{-1}\sum_z(c_i(z)-1)^2\to0$.

For **every** pair of laws in the first condition, the extracted sets can be chosen so that $P_i$ and $Q_i$ approach the fair laws on $S_i$ and $T_i$ in total absolute mass. The two sets are eventually nonempty. In particular almost every residue has exactly one representation from their product, and the squared errors at the exceptional residues have total $o(M_i)$. [Extraction and equivalence](Green33BalancedRectangles.lean)

## How to find the two sides

Write $r=\sqrt M$ and split the common labels into $U$ and $V$ according to which input assigns more mass, breaking ties consistently. Write $w=P(V)+Q(U)$. The squared overlap estimate bounds $w^2$ by $(|A|/r)(1/r+\sqrt D)$. A probability rectangle indexed by $X,Y$ satisfies $P(X)Q(Y)\le |X||Y|/M+\sqrt D$. Applying these bounds to $U,V$ gives $w\to0$ and $|U||V|/M\ge1-o(1)$. Since $|U|+|V|\le(2+o(1))r$, both side lengths divided by $r$ approach one. [Partition and rectangle bounds](Green33WeightedPeaks.lean)

Remove the labels in $U$ with $rP(x)<1-2e$, and do the same in $V$ with $Q$. Choose $e>0$ tending to zero slowly enough to dominate the side-length errors and the square root of the slack in the rectangle bound. The finite trimming inequality limits the number removed from each side to $er$. On the remaining sides, each pair contributes at least $(1-2e)^2/M$ to its output atom. Their unweighted collision energy is therefore at most $M(1+D)/(1-2e)^4$. Their product size is asymptotic to $M$, so the mean squared count error tends to zero. [Finite trimming and energy inequalities](Green33BalancedRectangles.lean)

For the converse, put $y=|S||T|/M$ and use the fair laws on $S,T$. Their sum probabilities are $c(z)/(|S||T|)$, giving the exact identity

\[
 y^2 D+(1-y)^2=\frac1M\sum_z(c(z)-1)^2.
\]

Here $y\to1$. The identity also records the cost of a rectangle whose product size differs from the group order. [Fair-law identity](Green33BalancedRectangles.lean)

## Relation to Green 33

The pinned conjecture asks for ordinary cyclic two-bases at coefficient $\sqrt2$. The notebook's weighted equivalent asks for vanishing total variation at that coefficient. Earlier bounds force the Pearson divergence there to have lower limit at least $1/2$. The theorem above treats the threshold coefficient two for **vanishing Pearson divergence**. It complements the exact classification at square orders. Classical group near-factorizations have unique representations away from one missing element. Here the exceptional set may grow and its total squared error is controlled. [Pinned source](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Weighted equivalence](WEIGHTED-STABILITY.md) · [Lower bound](WEIGHTED-SUM-PEAKS.md) · [Exact minimum](SQUARE-ORDER-TILINGS.md) · [Near-factors of finite groups](https://combinatorialpress.com/ars-articles/volume-029-ars-articles/near-factors-of-finite-groups/)

The DeepMind source issue closed with its statement formalization. Left to Solve listed no solution. Targeted tracker searches in DeepMind, Open Math Agents and the personal notebook found no matching Lean result. [Source issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Formalization PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents/issues?q=%22chi-squared%22+%22tiling%22)

Replay **Green33BalancedRectangles** with the [notebook runner](../../scripts/replay-research). Seven modules underwent fresh Lean 4.33.1 compilation and independent kernel replay. The 64 printed axiom sets contain only subsets of the standard three axioms.
