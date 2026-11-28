# Green 33 · Low-rank approximations of the representation table

Let $A\subseteq\mathbb Z/M$ have $k$ elements. Write $r(z)$ for the number of **ordered** pairs in $A^2$ with sum $z$, including the diagonal, and put $H_{ij}=r(i-j)$. Suppose $M\to\infty$, $k/\sqrt M\to\sqrt2$, and $|A+A|/M\to1$. For every fixed $C$ and every $L<2$, eventually **every** real matrix $B$ of rank at most $C\sqrt M$ satisfies
\[
 \frac1{M^2}\sum_{i,j}(H_{ij}-B_{ij})^2>L .
\]
The fit can depend on the basis and the modulus. Its columns may use different coefficients in any chosen subspace of dimension at most $C\sqrt M$. The table can approach the constant two in mean absolute error under the same assumptions. Squaring the error detects the exceptional counts. [Finite and limiting theorems](Green33LowRank.lean) · [Absolute deviation bound](SHIFT-VARIATION.md)

## Finite bound

Let $d(z)$ count ordered differences, $D_1=\sum_z|r(z)-2|$ and $E=\sum_{i,j}(H_{ij}-B_{ij})^2$. For every finite abelian group of order $M$,
\[
 M(k-2)\le \sqrt{M E}+(\operatorname{rank}B+1)D_1 .
\]
In particular, whenever $D_1>0$, a proposed fit of error $E$ requires rank at least $(M(k-2)-\sqrt{M E})/D_1-1$. The finite inequality also covers $D_1=0$. [`finite_rank_bound`](Green33LowRank.lean)

To prove it, center the sum table and the difference table by subtracting two from every entry. Call the resulting matrices $R$ and $T$. The two profiles have equal autocorrelations at each shift and equal total mass, so $R^\mathsf{T}R=T^\mathsf{T}T$. Thus $\|Ru\|=\|Tu\|$ for every vector $u$. Convolution by $r-2$ is a weighted sum of coordinate translations, each an isometry, giving $\|R\|_{\rm op}\le D_1$. Meanwhile $\operatorname{tr}(T)=M(k-2)$ since $d(0)=k$. [Autocorrelation identity](Green33ShiftVariation.lean) · [Matrix proof](Green33LowRank.lean)

Write $K$ for $B$ centered in the same way. In an orthonormal basis adapted to $\ker K$, each kernel vector $u$ contributes at most $\|(R-K)u\|$ to the trace of $T$. The orthogonal complement has dimension $\operatorname{rank}K$, and each of its basis vectors contributes at most $D_1$. Cauchy–Schwarz bounds the sum of the kernel contributions by $\sqrt{ME}$. Centering $B$ adds at most one to its rank. Finally, the finite deviation estimate gives $D_1=o(M)$ at the stated size and coverage. After division by $M^{3/2}$, the rank term vanishes and $\liminf \sqrt E/M\ge\sqrt2$. [`trace_rank_bound` and `low_rank_residual`](Green33LowRank.lean) · [Deviation estimate](Green33ShiftVariation.lean)

## Scope and sources

Green's pinned declaration asks for full sumset coverage on unbounded cyclic orders at coefficient $\sqrt2$. The theorem `green_low_rank_residual` applies to every family with exactly this coverage and limiting size. Existence remains open. The earlier Fourier theorem bounds individual character coefficients. Eckart and Young describe optimal low-rank approximation in general. The present estimate uses the trace of the difference table and near-coverage to give a numerical lower bound for the entire sum table. [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Earlier Fourier estimate](FOURIER-STABILITY.md) · [Eckart and Young (1936)](https://doi.org/10.1007/BF02288367)

Duplicate checks covered the DeepMind statement issue and formalization PR, Left to Solve, Open Math Agents, and the personal notebook. The personal hereditary estimate concerns deletion of labels. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Formalization PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents/issues?q=%22Green33%22) · [Hereditary bound](HEREDITARY-TAIL.md)

Replay `Green33LowRank` with the [notebook runner](../../scripts/replay-research). Seven notebook modules passed clean Lean 4.33.1 elaboration and separate kernel replay. All 47 axiom reports use only `propext`, `Classical.choice` and `Quot.sound`.
