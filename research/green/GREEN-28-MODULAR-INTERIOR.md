# Green 28 with one commensurable marginal of dyadic width

Let $P,Q$ be independent integer laws with a uniform sum. Suppose the width $D=\max\operatorname{supp} P-\min\operatorname{supp} P$ is a power of two and the ratios of positive interior atom masses of $P$ are rational. Then both laws are uniform if **either** of the following holds.

- The width of $Q$ is at most $2D$, including equality.
- The least atom of $Q$ is the only occupied site in its residue class modulo $D$. The width of $Q$ can then be arbitrarily large.

The masses of $Q$, the number of atoms in each marginal, and the interior-to-endpoint ratios of $P$ are unrestricted. The theorem `Green28ModularInterior.uniform_of_dyadic_interior` uses the pinned definitions of independent sum and uniformity for integer PMFs. Its width and support assumptions concern the original two laws. The general Green 28 conjecture remains open. [Lean statements and proofs](Green28ModularInterior.lean) · [Pinned Green 28](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean)

## A rational remainder

Normalize the two probability polynomials to monic $f,g$ with constant term one and binary product $H=fg$. At any occupied interior index of $f$, let $u$ be its normalized mass. Commensurability gives
\[
  f=A+uL,\qquad A=1+X^D,
\]
with $L$ a nonzero rational polynomial of degree less than $D$. When $D=2^k$, $A=\Phi_{2^{k+1}}$ is irreducible over $\mathbb Q$. Hence $\gcd(A,L)=1$. Choose rational polynomials $s,t$ with $sL+tA=1$. Modulo $A$, this gives $ug\equiv sH$. Taking the rational remainder of $sH$ produces
\[
  ug=T+A K,\quad T\in\mathbb Q[X],\quad \deg T<D.
\]
The checked Bézout argument applies to every rational monic $A\ne1$ coprime to $L$. [Interior shape of one marginal](Green28InteriorRatios.lean) · [Remainder and cyclotomic lemmas](Green28ModularInterior.lean)

## Reading the constant coefficient

In the bounded-width case $\deg K\le D$. The endpoint contribution to $H_D$ forces $g_D=0$. Comparing degrees $0,D,2D$ in the remainder identity gives
\[
 u=T_0+K_0,\qquad 0=K_0+K_D,\qquad u g_{2D}=K_D.
\]
Thus $T_0=u(1+g_{2D})$. The factor in parentheses is either one or two, since $2D$ lies beyond the support of $g$ or is its leading index.

In the isolated-residue case, $g_{nD}=0$ for all positive $n$. The same identity gives $K_{nD}=-K_{(n-1)D}$. Eventually these coefficients vanish because $K$ is a polynomial, and descending the recurrence gives $K_0=0$. Thus $T_0=u$. Either argument proves that every positive normalized interior coefficient of $f$ is rational. The existing rational-factor theorem gives uniformity of both laws. [Rational-factor rigidity](Green28PolynomialReduction.lean)

## Prior work and replay

The previous two-sided theorem permits every width when both marginals have commensurable interior masses. The earlier double-width trinomial argument uses a single nonzero interior coefficient. The trinomial manuscript directed by Alessandro Baravelli treats arbitrary partner width for that shape. Here one marginal can have arbitrarily many interior atoms and the partner can have arbitrary real masses. Hare studies finite-degree coefficient patterns and Hasanbegović proves a separated-block criterion for the output. [Two-sided theorem](GREEN-28-INTERIOR-RATIOS.md) · [Double-width trinomial lemma](Green28OutputBoundary.lean) · [Trinomial manuscript, Theorem 1](https://hexagonmath.org/pdf/2611.00674v2) · [Hare](https://arxiv.org/abs/2307.07363) · [Hasanbegović](https://arxiv.org/html/2611.14596v1)

The live search covered the DeepMind issue and statement PR, the indexed Left to Solve entry, and both OMA reduction PRs including the open reduction's Lean source. Lean 4.33.1 rebuilt the pinned upstream module and all eight notebook modules. Each local module passed independent kernel replay. All 50 axiom reports list exactly `propext`, `Classical.choice` and `Quot.sound`. For focused replay from the pinned Lake environment, pass `Green28ModularInterior` to the notebook runner. [Runner](../../scripts/replay-research) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28) · [OMA first reduction](https://github.com/lefttosolve2/open-math-agents/pull/9606) · [OMA polynomial reduction](https://github.com/lefttosolve2/open-math-agents/pull/21793)
