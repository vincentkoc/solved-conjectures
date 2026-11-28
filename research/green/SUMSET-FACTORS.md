# Sumset factorizations of a critical cyclic basis

Let \(T\subseteq\mathbb Z/n\mathbb Z\) be a family of ordinary two-bases with \(n\to\infty\), \(k=|T|\), and \(k/\sqrt n\to\sqrt2\). Give \(X,Y\subseteq\mathbb Z/n\mathbb Z\) arbitrary shapes, and write \(a=|X|,\ b=|Y|,\ e=|T\cap(X+Y)|\).

- If \(a,b\to\infty\) and \(e\ge\eta k\) for some fixed \(\eta>0\), then \(ab/k\to\infty\). In particular, \(ab=O(k)\) forces \(e=o(k)\).
- Uniformly over all relative factor sizes with \(ab=O(k)\), the positive part of \(e-\max(a,b)\) is \(o(k)\). The same estimate holds for bases whose sumset merely covers \(1-o(1)\) of the modulus.
- If \(T\subseteq X+Y\) and \(ab\le Ck\), then eventually \(\min(a,b)\le\lfloor C\rfloor\). The Lean statement gives \(\min(a,b)<r\) for each positive integer \(r>C\). For integral \(C\ge1\), the threshold is attained by taking \(Y=T\) and any \(C\)-element \(X\) containing zero, once \(k\ge C\).

These statements allow arbitrary extra elements in \(T\) and repeated sums in \(X+Y\). They also apply to quasi-Sidon families in additive commutative monoids, meaning that \(|T+T|=(1-o(1))\binom{k+1}{2}\) as \(k\to\infty\). For Green 33 this follows from full ordinary coverage and the size limit. Erdős and Freud use the quasi-Sidon condition for integer sequences. Erdős and Newman study the related problem of covering a prescribed integer set by \(B+B\). Here the two factors can differ, and the result also measures partial coverage. [Limit theorems](Green33FactorDensity.lean) · [Erdős and Freud, *On sums of a Sidon-sequence*](https://www.sciencedirect.com/science/article/pii/0022314X9190083N) · [Erdős and Newman, *Bases for sets of integers*](https://www.renyi.hu/~p_erdos/1977-05.pdf)

## Finite estimate

Put \(\Delta=\binom{k+1}{2}-|T+T|\), \(m=\min(a,b)\), \(M=\max(a,b)\). The diagonal counts once as an unordered pair. In every additive commutative monoid,
\[
e^2\ \le\ M e+ab(m+2\sqrt{\Delta}),\qquad
(e-M)_+^2\ \le\ ab(m+2\sqrt{\Delta}).
\]
For a square \(s\)-by-\(s\) grid and a Sidon set this gives \(e\le s+s^{3/2}\). A companion bound from two applications of Cauchy–Schwarz is
\[
e^4\le a^2b^2\bigl(ab(a+b)+4\Delta\bigr).
\]
[Finite inequalities](Green33SumsetFactors.lean)

Select one cell \((x,y)\) for each occupied label \(x+y\in T\). These cells form a bipartite graph between \(X\) and \(Y\). Each rectangle with distinct rows and columns has two diagonals. The two unordered pairs of labels on its diagonals are distinct and have the same sum. Each diagonal pair determines its rectangle because the selected cells have distinct labels. Keeping one unordered pair for each sum therefore loses at least one pair per rectangle. The number of rectangles with both row and column order specified is at most \(4\Delta\). This constant is sharp, even for a full cyclic basis. Modulo 9, \(X=\{0,1\}\) and \(Y=\{0,3\}\) give one rectangle, and \(T=X+Y\) has just one extra unordered representation, \(0+4=1+3\). [Sharpness certificate](Green33SumsetFactors.lean)

For each ordered pair of distinct rows, let \(d\) count their common columns. Summing \(d(d-1)\) counts the ordered rectangles. Cauchy–Schwarz applied to \((d-1)_+\) bounds the sum of all \(d\) by \(a^2+2a\sqrt{\Delta}\). The sum of squared column degrees is \(e+\sum d\). Applying Cauchy–Schwarz to the column degrees and then placing the smaller factor on the row side gives the finite estimate. This uses the classical four-cycle counting argument in extremal bipartite graph theory. The additive step charges cycles directly to \(\Delta\), allowing arbitrarily large representation counts at individual sums. [Kővári, Sós and Turán, *On a problem of K. Zarankiewicz*](https://doi.org/10.4064/cm-3-1-50-57)

If \(ab\le Ck\), then \(m\le\sqrt{Ck}\). Dividing the finite estimate for \((e-M)_+^2\) by \(k^2\) gives the uniform limit whenever \(\Delta=o(k^2)\). If both factors grow then \(M/k\le C/m\to0\). If \(e=k\), then \(M\ge(1-o(1))k\), giving the asserted integer threshold for \(m\).

## Scope and verification

The pinned declaration asks for infinitely many positive moduli carrying a full basis within every positive absolute tolerance of \(\sqrt2\). These implications concern every sequence of such witnesses at vanishing tolerances. They impose no geometric, subgroup, or digit assumptions. The notebook's earlier piece obstruction instead bounds covers by a fixed number of sets with small self-sumsets. [Pinned declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Piece obstruction](PIECE-OBSTRUCTION.md) · [Translation overlaps](TRANSLATE-OVERLAP.md)

A finite check evaluated both stability inequalities and the fourth-power bound on all 2,396,744 triples \(T,X,Y\), including empty factors, over the cyclic groups of orders 1 through 7. DeepMind and Open Math Agents tracker searches returned no matching factor-cost theorem. Left to Solve lists the parent problem and its solved feed has no Green 33 entry. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents) · [Left to Solve](https://www.lefttosolve.com/api/problems/Green33.green_33)

Lean 4.33.1 rebuilt all four modules in the import closure and replayed them with the independent kernel checker. All 23 printed declarations use only `propext`, `Classical.choice` and `Quot.sound`. A separate replay used the canonical positive modulus, full sumset and vanishing absolute tolerances to deduce the divergent factor cost. [Notebook replay](../README.md#replay)
