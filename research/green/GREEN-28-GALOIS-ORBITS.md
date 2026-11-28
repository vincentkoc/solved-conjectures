# Green 28 for a two-homogeneous irreducible factor

Let independent integer random variables have a sum uniform on the finite nonempty set $S$. Shift $S$ by its minimum and form its binary generating polynomial $M$. Both original laws are uniform if
\[
   M\mid H^k(X^m-1)^e \quad\text{in }\mathbb Q[X],
\]
where $m>0$, $H$ is monic irreducible with $H(0)\ne0$, and its Galois group acts transitively on unordered pairs of distinct roots. The degree of $H$ and the exponents $k,e$ are arbitrary. The polynomial version allows any nonzero real padding with all complex roots on the unit circle. [Lean statements and proofs](Green28GaloisOrbits.lean) · [Pinned Green 28](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean)

## Why the root multiplicities matter

Write $D$ for a monic complex divisor of $H^k$ with $D(0)=\pm1$. For each root $\alpha_i$ of $H$, let $w_i$ be its multiplicity in $D$ and put $u_i=\log|\alpha_i|$. The constant coefficient fixes $\prod_i(-\alpha_i)^{w_i}$ under every Galois automorphism. Consequently $\sum_i w_i u_{\sigma i}=0$ for every $\sigma$.

The real matrix with entries $\sum_\sigma u_{\sigma i}u_{\sigma j}$ has one diagonal value $A$ and one off-diagonal value $B$. If $u$ varies, $2(A-B)$ is a positive sum of squares. Comparing two rows against $w$ gives $(A-B)(w_i-w_j)=0$. Thus $D=H^t$ for some $t\le k$. If $u$ is constant and $D$ has a root, its unit constant coefficient forces the common modulus to be one. The constant divisor has an empty root set. [Orbit sum and divisor dichotomy](Green28GaloisOrbits.lean)

Split a normalized real marginal polynomial into a divisor of $H^k$ and a divisor of the padding. The second piece is reciprocal up to a sign, so the first has constant coefficient $\pm1$. The dichotomy gives either a marginal whose roots all have modulus one, or a rational factor times a reciprocal factor up to a rational sign. The earlier reversal criterion gives binary coefficients for both marginals in either case. The PMF transport uses the upstream definitions of independence and uniformity directly. [Reversal criterion](GREEN-28-REVERSAL-FIELD.md) · [Normalized PMF factors](Green28UniformSums.lean)

## A family of composite degrees

For odd $n\ge3$, let $H=X^n-X+1$. Nart–Vila and independently Osada give the full symmetric Galois group for $X^n-X-1$. Substituting $-X$ and changing sign gives the same conclusion for $H$. The binary polynomial
\[
   (1+X+\cdots+X^{n-1})H=1+X^{n+1}+\cdots+X^{2n-1}
\]
satisfies the divisibility condition with $k=e=1$ and $m=n$. Thus the condition includes asymmetric masks with a composite-degree irreducible factor, starting in this odd family at $n=9$. Multiplying by $1+X^{2n}$ gives two disjoint copies of the support and an example realized by two nonconstant independent laws. Its cyclotomic part divides $(X^{4n}-1)^2$. The Lean theorem takes the Galois hypothesis as input. The group computation for this family comes from the literature. [Osada, Theorem 1 and p. 441](https://doi.org/10.2748/tmj/1178228289) · [Conrad, Theorem 2.1 and references](https://kconrad.math.uconn.edu/blurbs/gradnumthy/galoisselmerpoly.pdf)

## Attribution and verification

Multiplicative relations between conjugate roots have a substantial literature. Zheng's Theorem 3.2 proves triviality of the rational exponent lattice for a two-homogeneous action when some root has no positive rational power. The Lean proof above needs only log-moduli and also treats the constant-modulus case directly. The contribution here is the kernel-checked divisor dichotomy and its application to Green's integer PMFs. The unrestricted conjecture remains open. [Zheng, Theorem 3.2](https://arxiv.org/pdf/1912.07202) · [Hasanbegović's related support criteria](https://arxiv.org/html/2611.14596v1)

The live search covered the DeepMind issue and statement PR, Left to Solve, OMA's two reductions and the personal notebook. Under Lean 4.33.1 the pinned declaration and nine local modules were rebuilt from source. All nine local modules passed independent kernel replay, and the 52 axiom reports list exactly `propext`, `Classical.choice` and `Quot.sound`. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28) · [OMA first reduction](https://github.com/lefttosolve2/open-math-agents/pull/9606) · [OMA polynomial reduction](https://github.com/lefttosolve2/open-math-agents/pull/21793)
