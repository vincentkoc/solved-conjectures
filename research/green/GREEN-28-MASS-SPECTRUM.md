# Green 28 · A finite set of atom probabilities

Fix a natural number $k$. There is a finite set $A_k$ of real numbers containing every atom probability of either marginal of **every** uniform independent integer sum with at most $k$ outcomes. The spacing of the outcomes and the integer positions of the marginals are arbitrary. If the output has exactly $m$ outcomes, then $mP(x)$ and $mQ(y)$ are algebraic integers for all $x,y$. [Finite alphabet and integrality theorems](Green28MassSpectrum.lean)

## Which probabilities enter the set

For a nonempty output support $S$, shift its least element to zero and write $H$ for the resulting polynomial with coefficients zero and one. The normalized marginal models give a monic factorization $H=fg$ over the reals. Summing all masses in the law represented by $f$ gives the mass at offset $j$ as $f_j/f(1)$. Since $H(1)=m$, this yields
$$
m\,P(x)=f_j g(1).
$$
Every coefficient of a monic divisor of the monic integer polynomial $H$ is integral over the integers. So are $g(1)$ and the displayed product. Unoccupied sites contribute zero. The argument also proves the integrality bound for all catalogue entries obtained from monic real divisors, including those with signed coefficients. [Coefficient normalization and catalogue](Green28MassSpectrum.lean)

A nonzero polynomial has finitely many monic real divisors. List the normalized nonzero coefficients of all of them and include zero. This gives a finite list for a fixed mask. To obtain $A_k$, take the union over the nonempty sets of at most $k$ sites in $[0,5^{k+1}]$ and include zero. Every original law has a relabelling into that interval that preserves occupied-site masses and the uniform sum. Consequently $k!A_k$ consists of algebraic integers. The product of their minimal polynomials gives one monic integer polynomial annihilating all the scaled entries. The catalogue can contain values that no probability law realizes. [Compression](Green28FiniteSearch.lean) · [Common polynomial](Green28MassSpectrum.lean)

## Scope of the reduction

`Green28MassSpectrum.green_28_iff_alphabet_tests` has the literal type of the pinned declaration on its left. For each $k$ the right side tests vectors indexed by $[0,5^{k+1}]$ and taking values in $A_k$. They must be probability vectors, and their convolution must agree with the target at every possible sum site. Every feasible real pair is realized by integer laws and therefore occurs among these finite tables. The definitions use classical finite sets of real algebraic numbers. An executable root-isolation implementation and the truth of the tests at arbitrary budgets remain open here. [Formal theorem](Green28MassSpectrum.lean) · [Earlier real-vector tests](GREEN-28-FINITE-TEST.md) · [Pinned Green 28](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean)

Bausch and Cubitt give the finite-distribution/polynomial factorization correspondence in Proposition 50 and Lemma 51. Hare studies the coefficient patterns of candidate factors of binary polynomials. The earlier notebook proved algebraicity of the probabilities and a bound on support positions in terms of the output count. [Bausch and Cubitt](https://pmc.ncbi.nlm.nih.gov/articles/PMC5465997/) · [Hare](https://arxiv.org/abs/2307.07363) · [Arithmetic of uniform sums](GREEN-28-ARITHMETIC.md)

The DeepMind issue and statement PR, Left to Solve record, and OMA reductions and special cases were checked for overlap. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28) · [OMA first reduction](https://github.com/lefttosolve2/open-math-agents/pull/9606) · [OMA second reduction](https://github.com/lefttosolve2/open-math-agents/pull/21793) · [Two-site case](https://github.com/lefttosolve2/open-math-agents/pull/27234) · [Low-degree coefficient case](https://github.com/lefttosolve2/open-math-agents/pull/29600)

A clean build from the pinned source and independent Lean 4.33.1 kernel replay checked all nine notebook modules. All 73 printed declarations used only `propext`, `Classical.choice` and `Quot.sound`. Replay `Green28MassSpectrum` with the [notebook runner](../../scripts/replay-research).
