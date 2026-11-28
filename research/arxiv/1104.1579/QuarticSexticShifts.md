# Positive constant shifts in degrees four and six

Let $P_j(X)=m+X+X^2+\cdots+X^j$ for a positive integer $m$. Then $P_6$ is irreducible over $\mathbb Q$ for every $m$. The quartic $P_4$ is irreducible over $\mathbb Q$ exactly when $m\ne12$. The exceptional factorization is
$$
X^4+X^3+X^2+X+12=(X^2+3X+4)(X^2-2X+3).
$$
In particular $P_6$ is irreducible at every positive Jones parameter $t$, with $m=2\lfloor(2^t+1)/3\rfloor$. For the odd parameters in Jones’s Conjecture 4.1 the division by three is exact. The earlier power-of-two degree theorem already covers $P_4$ for Jones’s own constants. [Classification](CunninghamJonesQuarticSextic.lean) · [Jones, Conjecture 4.1](https://arxiv.org/pdf/1104.1579#page=7) · [Power-of-two degrees](JonesPrimePowerDegrees.md)

## The sextic discriminant

For $m\ge2$ every real value of $P_j$ is positive when $j$ is even. Thus every monic integral factor has even degree. A proper factorization of a quartic or sextic must have a monic quadratic factor $X^2+aX+b$. The case $m=1$ gives the fifth and seventh cyclotomic polynomials. [Even-degree factors](CunninghamJonesFactorOrders.lean) · [Prime-power predecessor test](CunninghamJonesPrimePowerDegrees.lean)

In degree six, the coefficient of $X$ in the remainder modulo $X^2+aX+b$ must vanish. Multiplying out the putative factors gives
$$
(1-3a)b^2+(4a^3-3a^2+2a-1)b+1-a+a^2-a^3+a^4-a^5=0.
$$
Its discriminant in $b$ must be an integer square:
$$
D(a)=4a^6-8a^5+9a^4-4a^3-6a^2+12a-3.
$$
Set $T=8a^3-8a^2+5a+1$. Then
$$
16D(a)=T^2-(105a^2-182a+49).
$$
For $|a|\ge20$, the correction is strictly between zero and $2|T|-1$. Consequently $16D(a)$ lies strictly between consecutive squares. Lean checks the two inequalities by substituting $a=20+k$ or $a=-20-k$, with $k\ge0$. For the 39 remaining integers the exact integer square root gives $a=-1$ or $a=1$. The only possible pairs $(a,b)$ are $(-1,1),(1,0),(1,1)$. In each case the coefficient equations force $m=0$. [Square discriminants](CunninghamJonesSexticDiscriminant.lean) · [Factor equations](CunninghamJonesQuarticSextic.lean)

In degree four write the two quadratic factors as $X^2+aX+b$ and $X^2+(1-a)X+d$. Comparing coefficients gives $b=1+a(b-d)$, $d=1+(a-1)(b-d)$, and
$$
(2a-1)\big((2a-1)-4(b-d)\big)=5.
$$
The first factor divides five. Substituting its four possible integer values yields $bd=0$ or $bd=12$. The displayed factorization realizes the only positive exception. [Quartic coefficient argument](CunninghamJonesQuarticSextic.lean)

## Scope and verification

The pinned DeepMind declarations ask for infinitely many natural prime seeds of each exact positive chain length under $q\mapsto 2q+1$ and $q\mapsto 2q-1$. The polynomial classification settles the degree-six case of Jones’s related polynomial conjecture. Both integer infinitude statements and the general polynomial conjecture remain open. [Pinned declarations and hypotheses](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean) · [Jones](https://arxiv.org/abs/1104.1579)

An independent calculation reduced both geometric sums by Horner’s rule modulo 2,666,700 candidate monic quadratics. For $1\le m\le10{,}000$, a quadratic factor has $1\le b\le10{,}000$ since $b$ divides $m$ and nonreal conjugate roots have positive product. Its negative discriminant gives $a^2<4b$. These bounds enumerate every candidate in that range. Only the two displayed factors at $m=12$ occurred.

Lean 4.33.1 rebuilt and independently kernel-replayed all six notebook modules in the dependency closure. All 24 named axiom reports use only `propext`, `Classical.choice` and `Quot.sound`. The main declarations are `CunninghamChain.jones_sextic_irreducible`, `CunninghamChain.jones_parameter_sextic` and `CunninghamChain.jones_quartic_irreducible_iff`. The notebook index check and five repository tests passed. The pinned upstream file matches the live blob. Searches of DeepMind and Open Math Agents issues and pull requests and 11,353 Left to Solve records found the integer-chain issue, its statement PRs and related reductions. No matching formalization of these classifications appeared. Codex assisted with the proof. [Notebook replay](../../README.md#replay) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/4755) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/4765) · [Other statement PR](https://github.com/google-deepmind/formal-conjectures/pull/4770) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents) · [Left to Solve](https://lefttosolve.com/api/solved)
