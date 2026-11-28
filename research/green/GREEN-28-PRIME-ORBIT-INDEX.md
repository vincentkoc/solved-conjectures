# A prime-field test for indecomposable uniform integer laws

Let independent integer laws $P,Q$ have a sum uniform on a finite nonempty set $S$. Translate the minimum of $S$ to zero and form its monic support polynomial $H$. For a prime $p$, suppose the reduction of $H$ factors in the algebraic closure of $\mathbb F_p$ as
\[
       \prod_{i=0}^{d-1}(X+\beta^{p^i}),\qquad
       n=\operatorname{ord}(\beta),\qquad nc=L=1+p+\cdots+p^{d-1}.
\]
The constant of each displayed linear factor is a conjugate of $\beta$. The sign matters in odd characteristic. **If $c\le 2p$, one of $P,Q$ is a point mass** and both laws are uniform on their supports. At the smaller threshold $c\le p$, the polynomial conclusion holds even for monic real factors with arbitrary coefficient signs. A factor with constant term one has degree zero or $d$. Roots in the displayed product are counted with multiplicity. [Prime-index theorems](Green28PrimeOrbitIndex.lean) · [Pinned Green 28](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean)

## Two uniform laws on genuine sumsets

Both examples have width sixteen. The equalities below describe their supports. In both cases every independent decomposition of the **uniform law** has a constant input.

| Output support | A decomposition of the set | Signed root order in characteristic three | Index |
| --- | --- | --- | --- |
| $\{0,1,2,4,5,6,13,14,15,16\}$ | $\{0,4,13,14\}+\{0,1,2\}$ | $10\,761\,680$ | $2$ |
| $\{0,\ldots,16\}\setminus\{3,6,7\}$ | $\{0,1,2,4,5\}+\{0,8,9,10,11\}$ | $5\,380\,840$ | $4$ |

The fourteen-site example uses the larger threshold. Both masks have a root at one modulo two. If either were a single binary Frobenius orbit, all its roots would then equal one. Its reduction would be $(X+1)^{16}=X^{16}+1$, contrary to its coefficient of $X$. Lean verifies both support equalities, both ternary certificates, both point-mass conclusions and both exclusions of a binary orbit. The earlier result for at most eleven outcomes already gives marginal fairness for the ten-site example. [Example proofs](Green28TernaryExample.lean) · [Binary orbit criterion](GREEN-28-BALANCED-ORBITS.md) · [Eleven-output theorem](GREEN-28-ELEVEN-OUTPUTS.md)

For the first ternary certificate write $x$ for the negative of a root. The proof verifies $x^{10\,761\,680}=1$. For each prime divisor $q\in\{2,5,17,41,193\}$, it verifies a multiplicative inverse of $x^{10\,761\,680/q}-1$. The second signed root is $x^{381386}$ in the same field. Its order is half the first, and evaluating the second polynomial at its negative gives zero. Each case has sixteen distinct Frobenius exponents modulo its order. The certificate tables store powers by their base-three coefficients. The kernel verifies their squarings, multiplications and evaluations. [Certificate arithmetic](Green28TernaryExample.lean)

## Why the index controls the widths

The normalized marginal polynomials are monic factors of $H$ with nonnegative real coefficients and constant terms one. Reducing their algebraic-integer coefficients at a maximal ideal over $p$ preserves both degrees and the product. The reduced first factor selects a set of places $U\subseteq\{0,\ldots,d-1\}$. Its constant term is $\beta^E$ for $E=\sum_{i\in U}p^i$. Hence $n\mid E$, and its degree is $|U|$. A nonempty proper selection would give $E=nj$ with $0<j<c$. Since $cE=jL$ and $L\equiv1\bmod p$, the units digit gives $j\equiv0$ or $c\bmod p$. For $c\le p$, neither residue occurs strictly between zero and $c$. [Monic reduction](Green28PrimitiveSupport.lean) · [Frobenius and norm background, Lidl and Niederreiter, Chapter 2](https://www.cambridge.org/core/books/abs/finite-fields/structure-of-finite-fields/B800DF02E1774853AABCBF9129A24C7D)

For $c\le 2p$, the only possible indices are $p$ and $c-p$. Rotating the $d$ places by one gives $E'$ congruent to $pE$ modulo $M=p^d-1=(p-1)L$. The rotation stays nonempty and proper and still has $n\mid E'$. It changes the value since $0<(p-1)E<M$. Thus $E$ and $E'$ use different indices, which sum to $c$, and $E+E'=L$. In base $p$ the complement of $U$ encodes $L-E$. Uniqueness of expansion makes the rotation equal to that complement, so both factors have degree $d/2$. At this degree their real product receives one from each pair of opposite endpoints. Nonnegativity contradicts the binary output coefficient. [Digit selection and endpoint proof](Green28PrimeOrbitIndex.lean)

## Scope and replay

The hypothesis restricts the observed output support. The formal statements use the original independent-sum and uniformity predicates. The input sizes, representation counts and probability ratios are unrestricted. The general conjecture remains open. The live duplicate check covered the DeepMind issue and statement PR, the Left to Solve entry, the OMA reductions, the two-site submission and the personal notebook. Hare's computations test coefficient patterns of prospective factors. These sources did not supply the prime-index theorem or the ternary certificates above. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28) · [OMA first reduction](https://github.com/lefttosolve2/open-math-agents/pull/9606) · [OMA second reduction](https://github.com/lefttosolve2/open-math-agents/pull/21793) · [OMA two-site submission](https://github.com/lefttosolve2/open-math-agents/pull/27234) · [Hare](https://arxiv.org/abs/2307.07363)

Lean 4.33.1 rebuilt the seven modules in a clean directory and the independent checker replayed them sequentially. All 58 printed axiom reports listed only `propext`, `Classical.choice` and `Quot.sound`. Run `Green28TernaryExample` with the [notebook replay runner](../../scripts/replay-research) in the pinned Lake environment.
