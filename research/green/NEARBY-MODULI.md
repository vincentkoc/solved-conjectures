# Green 33 and the loss at nearby moduli

Let $N\to\infty$, let $A\subseteq\mathbb Z/N\mathbb Z$, and let $B\subseteq[0,N)$ contain the least representatives of $A$. Assume $|A|/\sqrt N\to\sqrt2$ and $|A+A|/N\to1$. For **every** $\varepsilon>0$ and every sufficiently large member of this family, there is an integer
\[
 N<m\le(1+\varepsilon)N,\qquad
 \frac{|(B+B)\bmod m|}{m}\le\frac56+\varepsilon .
\]
Here $B$ stays fixed as the modulus changes. An exact Green basis meets the coverage hypothesis. The existence of the conjectured family remains open. [Nearby-modulus theorem](Green33NearbyModuli.lean) · [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

## The band formula

Put $C=B+B$ with ordinary integer addition, including diagonals, and $L_m=|C|-|C\bmod m|$. For integer endpoints $N\le a\le b$ with $a/N\to s$, $b/N\to t$ and $1\le s\le t<2$,
\[
 \frac1{N^2}\sum_{m=a}^{b-1} L_m
 \longrightarrow \frac{(2-s)^4-(2-t)^4}{24}.
\]
Since $C\subseteq[0,2N)$, $L_m$ counts pairs $(x,x+m)$ in $C^2$ exactly. Summing therefore counts each positive gap in the band once. Taking $a=N+1$ and $b=\lfloor(1+\delta)N\rfloor+1$, the limiting average of $L_m/N$ is $(1-(1-\delta)^4)/(24\delta)$. It tends to $1/6$ as $\delta$ decreases to zero, while $|C|/N\to1$. This gives the stated witness. The theorem permits exceptional moduli and gives no bound below one on the coverage achieved by a different seed at $m$. [Gap count, band limit and witness](Green33NearbyModuli.lean)

## Why the constant appears

The size and coverage assumptions force the ordered cyclic representation counts to have total absolute deviation $o(N)$ from two. For the centered seed indicator $f$, this gives $\sum_x |(f*f)(x)|=o(N)$. The real circulant of $f$ commutes with its transpose. Applying Cauchy–Schwarz and a short shift average then bounds the error in counting $A$ inside any moving arc by $o(\sqrt N)$, uniformly over the arc's endpoints. [Representation error](Green33ShiftVariation.lean) · [Arc discrepancy](Green33ArcDistribution.lean)

Consequently the sorted label ranks differ from their uniformly spaced predictions by $o(\sqrt N)$. Reverse the two ranks giving the larger sum. A gap of at least $sN$ becomes a simplex test on four ranks. Stars and bars bounds the count between two binomial coefficients with thresholds differing by $o(\sqrt N)$. Removing every diagonal sum costs at most $|A|$ distinct values. Every remaining sum has both orderings, so the ordered quadruple count has four times the limiting mass of the distinct sum-pair count. [Rank comparison and simplex count](Green33RankSimplex.lean) · [Passage to distinct sums](Green33NearbyModuli.lean)

Erdős and Freud studied the distribution of sums of dense integer Sidon sets. Ortega and Prendiville give Fourier uniformity results for extremal integer Sidon sets. Here the assumptions concern the size and modular coverage of an arbitrary cyclic set, which may have many repeated representations. The closed DeepMind issue and its merged PR concern formalization of the original question. Targeted searches of DeepMind, Open Math Agents and the personal tracker found no matching nearby-modulus theorem. Left to Solve listed no solution to Green 33. [Erdős–Freud](https://doi.org/10.1016/0022-314X(91)90083-N) · [Ortega–Prendiville](https://doi.org/10.5802/jtnb.1239) · [Green issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33)

Replay **Green33NearbyModuli** with the [notebook runner](../../scripts/replay-research). The independent Lean 4.33.1 replay covered 16 notebook modules and 121 axiom reports. Exhaustive finite comparisons checked all 4,092 seeds at orders 2 through 11 and all 45,052 seed–gap choices from $N$ through $2N$.
