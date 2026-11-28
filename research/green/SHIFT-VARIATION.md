# Green 33 · Variation at every shift

Let $A\subseteq\mathbb Z/M$ and write $r(z)=|\{(a,b)\in A^2:a+b=z\}|$, with ordered pairs and diagonals included. Suppose $M\to\infty$, $|A|/\sqrt M\to\sqrt2$, and $|A+A|/M\to1$. For every fixed $B$, eventually **every nonzero shift** $h$ admits residues $x,y$ with
\[
r(x+h)-r(x)>B,\qquad r(y)-r(y+h)>B.
\]
The shift can vary with the seed and can have any order. The two jumps may occur at different residues. Moreover, for every $L<4$, eventually every nonzero $h$ satisfies $M^{-1}\sum_z(r(z+h)-r(z))^2>L$. Full bases in the pinned Green 33 statement satisfy the coverage hypothesis. Existence at the proposed size remains open. [`all_shift_jumps`, `all_shift_energy` and `green_shift_jumps`](Green33ShiftVariation.lean) · [Pinned conjecture](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

## Finite estimates

Write $d(h)=|\{(a,b)\in A^2:a-b=h\}|$ and $k=|A|$. The sum and difference counts have identical autocorrelation at **every lag**. Indeed, exchanging the second coordinates of two ordered pairs sends $(c+d)-(a+b)=h$ to $(c-b)-(a-d)=h$. Thus translation by $h$ changes the two profiles by the same squared norm. For $h\ne0$, the terms at $0$ and $-h$ in the difference profile alone give
\[
\sum_z(r(z+h)-r(z))^2\ \geq\ 2\big(k-d(h)\big)^2.
\]
The earlier translation-overlap theorem gives $\max_{h\ne0}d(h)=o(\sqrt M)$ under the hypotheses above. Division by $M$ yields the lower limit of four. [Autocorrelation and finite jump bound](Green33ShiftVariation.lean) · [Translation overlap](TRANSLATE-OVERLAP.md)

Let $D=\sum_z|r(z)-2|$. Every occupied sum has two ordered witnesses unless a diagonal supplies its only witness. Counting the diagonal labels gives
\[
D\le k^2+2M-4|A+A|+2k=o(M).
\]
If all upward changes $\Delta_z=r(z+h)-r(z)$ are at most $L\ge0$, translation invariance gives $\sum_z\Delta_z^2=2\sum_z(r(z+h)-2)\Delta_z$. Where $r(z+h)\ge2$, the summand before the factor two is at most $L|r(z+h)-2|$. Else it is at most $2|\Delta_z|$. Since $\sum_z|\Delta_z|\le2D$, the squared variation is at most $(2L+8)D$. This contradicts the energy lower bound for large $M$. Applying the upward conclusion to $-h$ supplies the downward jump. [`deviation_upper` and `one_sided_energy`](Green33ShiftVariation.lean)

## Periodic approximations

Let $H$ be a subgroup, let $q=|H|$ and let $f$ be any real function constant on its cosets. The same finite argument gives
\[
\sum_z (r(z)-f(z))^2 \ge (1-1/q)\big(k-\max_{h\ne0}d(h)\big)^2.
\]
To see this, sum the jump bound over $h\in H\setminus\{0\}$. The changes of $r-f$ agree with those of $r$ at those shifts. The sum of the autocorrelations of $r-f$ over $H$ is nonnegative, since it is a sum of squares of coset sums. The total squared change over $H$ is therefore at most $2q\sum_z(r(z)-f(z))^2$. Both the subgroup and the fitted function can be chosen after seeing the seed. For nontrivial $H$ the resulting mean squared residual has lower limit at least one, and at least two when $|H|\to\infty$. [`periodic_residual` and `all_periodic_errors`](Green33ShiftVariation.lean)

Sárközy studies the maximum absolute change of the ordered representation function at the unit shift in finite cyclic groups, relating it to the number of blocks of the seed. The statements here use the Green size and coverage assumptions and quantify both signed changes uniformly over all nonzero shifts. They are conditional restrictions on candidate families. The duplicate check covered the DeepMind issue and formalization PR, the Left to Solve record, Open Math Agents and earlier notebook results on peaks and translation overlap. [Sárközy, *On additive representation functions of finite sets, I (Variation)*](https://doi.org/10.1007/s10998-013-8476-6) · [Earlier peak divergence](DIVERGENCE.md) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Formalization PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents/issues?q=%22Green33%22+%22variation%22)

Replay `Green33ShiftVariation` with the [notebook runner](../../scripts/replay-research). Independent Lean 4.33.1 kernel checks cover six notebook modules and 43 axiom reports. Each lists only `propext`, `Classical.choice` and `Quot.sound`.
