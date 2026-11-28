# Green 28 for binary root orbits of smaller order

Let the independent integer laws $P,Q$ have a sum uniform on $S$. Shift the minimum of $S$ to zero and form the integer support polynomial $H(X)=\sum_{s\in S}X^{s-\min S}$, of degree $d>0$. Suppose that over $\mathbb F_{2^d}$ its reduction is
\[
H(X)=\prod_{i=0}^{d-1}(X-\alpha^{2^i}),
\qquad \operatorname{ord}(\alpha)=n,\quad cn=2^d-1.
\]
If $c\mid 2^k+1$ for some $k\ge0$, **one of $P,Q$ is a point mass**. Both laws are consequently uniform on their supports. The product lists its roots with multiplicity. An irreducible binary mask with a root of the stated order is a special case. [Formal statements](Green28BalancedOrbits.lean) · [Pinned Green 28](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean)

**Every positive even width has a nonprimitive example.** For $d=2t$ take $c=3$ and let $\alpha$ be the cube of a generator of $\mathbb F_{2^d}^\times$. Its order is $(2^d-1)/3$. The orbit product is fixed by squaring its coefficients, so they are binary. Its leading and constant coefficients are one. Lifting its support gives an integer mask of width $d$. Each root raised to $n$ gives one, ruling out a primitive root of order $2^d-1$. This construction includes $d=2$, where roots repeat. [Existence theorem](Green28BalancedOrbits.lean) · [Earlier primitive-mask criterion](GREEN-28-PRIMITIVE-SUPPORT.md)

## From root order to support widths

Normalize the two marginal generating polynomials to monic real factors $f,g$ with constant term one. The coefficients are algebraic integers. Reducing them at a maximal ideal over two preserves the product, the degrees and the constant terms. The reduced $f$ selects places $U\subseteq\{0,\ldots,d-1\}$ from the displayed product. Thus for **every** orbit order $n$, the width of the first marginal is the number of ones in a binary integer
\[
                       E=\sum_{i\in U}2^i,\qquad n\mid E.
\]
This restriction also applies without any hypothesis on $c$ apart from $cn=2^d-1$. [Real factor width theorem](Green28BalancedOrbits.lean) · [Monic reduction and PMF factors](Green28PrimitiveSupport.lean)

Write $M=2^d-1$. For a proper nonempty selection, $0<E<M$. If $c\mid 2^k+1$, then $M\mid(2^k+1)E$. Rotating the $d$ places by $k$ represents $2^kE$ modulo $M$. Its representative lies strictly between zero and $M$, as does the complement $M-E$. They agree, so the rotation sends the selected places to their complement. Therefore both factors have degree $d/2$. But at that degree the real product receives one from each pair of opposite endpoints. All other contributions are nonnegative, while each coefficient of $H$ is at most one. This eliminates every proper split. The complementary-digit phenomenon occurs in the literature on Midy's theorem, and the index condition is used for semiprimitive cyclic codes. [Lewittes, *Midy's Theorem for Periodic Decimals*](https://arxiv.org/abs/math/0605182) · [*On the weight hierarchy of the semiprimitive codes*](https://www.sciencedirect.com/science/article/pii/0012365X9400234A)

## A thirteen-site example

Take $S=\{0,1,2,4\}\cup\{6,7,\ldots,14\}$. The set itself is a nontrivial sumset:
\[
 S=\{0,1,2,4\}+\{0,6,9,10\}.
\]
Yet its uniform law forces a constant summand. The table gives the finite calculation for this example, separate from the kernel-checked general theorem. In the table each hexadecimal bit $i$ represents the coefficient of $X^i$ in the remainder modulo $H$ over $\mathbb F_2$.

| Exponent $j$ | $X^j\bmod H$ |
| --- | --- |
| 43 | `245b` |
| 127 | `1f53` |
| 128 | `3ea6` |
| 5,461 | `1` |
| 16,384 | `2` |

The polynomial gcds of $H$ with $X^4-X$ and with $X^{128}-X$ are both one. Since $14$ has prime factors two and seven, the final remainder and the two gcds prove irreducibility. Since $5461=43\cdot127$, the first, second and fourth remainders prove that a root has order $5461$. Its index is three, and $3\mid2+1$.

## Scope and replay

The point-mass theorem uses the original PMFs and the pinned independent-sum and uniformity predicates. The extra hypothesis concerns only the observed output support. The unrestricted fairness conjecture remains open. Live searches covered DeepMind's issue and statement PR, Left to Solve, the OMA reductions and the two-site submission. They found no matching root-index theorem for Green 28. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28) · [OMA first reduction](https://github.com/lefttosolve2/open-math-agents/pull/9606) · [OMA second reduction](https://github.com/lefttosolve2/open-math-agents/pull/21793) · [OMA two-site case](https://github.com/lefttosolve2/open-math-agents/pull/27234)

The five-module closure rebuilt with Lean 4.33.1 and passed independent kernel replay. All 37 printed axiom reports list `propext`, `Classical.choice` and `Quot.sound`. Use `Green28BalancedOrbits` with the [notebook replay runner](../../scripts/replay-research) in the pinned Lake environment.
