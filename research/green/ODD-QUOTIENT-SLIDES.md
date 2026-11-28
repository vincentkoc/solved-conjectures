# Green 33 · mean coverage after translating odd quotient layers

Let $m=2r+1$ be fixed. Suppose $A\subseteq\mathbb Z/N$ is a full two-basis along a sequence of multiples of $m$ with $N\to\infty$ and $|A|/\sqrt N\to\sqrt2$. Translate the elements of each residue class modulo $m$ together by an independent uniform multiple of $m$. Write $A_h$ for the translated set. Translation preserves its cardinality. The mean covered fraction has the limit
\[
\mathbb E_h\,\frac{|A_h+A_h|}{N}\ \longrightarrow\
1-\left(1-\frac1m\right)\left(1-\frac2m\right)^r.
\]
This gives $7/9$ for $m=3$. The constants tend to $1-e^{-1}$ through odd quotient orders. The kernel may have even order. The theorem controls the arithmetic mean over shifts. The zero shift always preserves full coverage. [Mean-coverage theorem and limits](Green33OddQuotientSlides.lean) · [Cardinality of the translated set](Green33OddRowSlides.lean)

**Connection with Green 33.** The pinned conjecture is equivalent to the existence of full critical bases $A_i$ on growing orders $N_i$ divisible by $2i+1$ for which the mean covered fraction tends to $1-e^{-1}$. For each fixed divisor the prescribed-divisor theorem supplies arbitrarily large full witnesses under Green's hypothesis. First take the large-order limit with that divisor fixed. Then choose the $i$th witness with error less than $1/(i+1)$ in both size and mean coverage. This selects a sequence of moduli and bases. Existence of a full critical sequence remains open. [Equivalence](Green33GrowingQuotientSlides.lean) · [Prescribed divisors](DIVISIBLE-ORDERS.md) · [Pinned ordinary-basis statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Green, problem 33](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.33)

## The finite count

Write $A_j$ for the original layer with label $j$. Above target label $2c$, there is one diagonal sum support $A_c+A_c$ and one mixed support $A_{c+j}+A_{c-j}$ per pair of opposite nonzero offsets. Put $k=N/m$. For a uniform target in this row and uniform independent shifts, the exact probability of a miss is
\[
\left(1-\frac{|A_c+A_c|}{k}\right)
\prod_{j=1}^r\left(1-\frac{|A_{c+j}+A_{c-j}|}{k}\right).
\]
The probabilities factor even with two-torsion in the kernel. Given a row target coordinate $x$ and shifts $h$, use coordinates $x-2h_c$ and $x-h_{c+j}-h_{c-j}$. Retaining $h_c$ and one shift per mixed pair makes this a bijection. This also works for finite abelian ambient groups with a surjection onto the given odd cyclic quotient. Independent translates and products of miss probabilities are classical. Here the supports are sums of layers, and each layer shift also determines the displacement of its diagonal sums. [Row coordinates](Green33OddSlideCoordinates.lean) · [Finite physical-row identity](Green33OddRowSlides.lean) · [Bollobás, Janson and Riordan, proof of Theorem 3.1](https://www2.math.uu.se/~svantejs/papers/sj240.pdf)

Oddness matters. In $\mathbb Z/4$, take $A=\{0,1\}$ and the quotient modulo two. Every layer slide covers both even residues with diagonal sums. Treating the two diagonal supports as independent would predict a missing fraction of $1/4$ on that row.

## Why the factors have limits

Fourier inversion on the quotient and the character bound for full bases give $|A_j|/\sqrt N\to\sqrt2/m$. A diagonal block has at most $\binom{|A_j|+1}{2}$ different sums, counting repeated summands. A mixed block has at most $|A_j||A_k|$ for $j\ne k$. In either block, its lost sums consume part of the ambient surplus $\binom{|A|+1}{2}-N=o(N)$. Thus the diagonal and mixed supports have relative densities $1/m$ and $2/m$ within their row. [Layer balance and pair budgets](Green33QuotientLayerBalance.lean) · [Ambient character bound](Green33FourierStability.lean) · [Diagonal pair budget](Green33BaerQuadraticRetention.lean)

The finite product count was also checked on every subset and target row for $(m,k)=(3,2),(3,3),(5,2)$, totaling 6,848 rows. The separate parity result gives convergence in probability under single-layer shifts. [Parity slides](PARITY-SLIDE-COVERAGE.md)

Replay with the notebook command and target `Green33GrowingQuotientSlides`. Codex assisted with the Lean proof. The exact conjecture remains listed as research open. [Replay instructions](../README.md#replay) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33) · [Open Math Agents search](https://github.com/lefttosolve2/open-math-agents/issues?q=%22Green33.green_33%22)
