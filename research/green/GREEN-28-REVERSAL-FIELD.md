# Green 28 and the field of reflected mass differences

Let $P,Q$ be independent integer laws with sum uniform on its support. Write $a=\min\operatorname{supp}P$, $b=\max\operatorname{supp}P$. For every real subfield $K$, all the point probabilities of **both** laws belong to $K$ if and only if
\[
\frac{P(a+b-z)-P(z)}{P(a)}\in K\qquad(z\in\mathbb Z).
\]
In particular, rationality of these differences forces both marginals to be uniform. The opposite marginal, the support sizes and the positions of the atoms are unrestricted. Only the differences of reflected masses have to be checked. This recovers the common probability field from half of the difference data, since exchanging the two reflected sites changes the sign. [`field_of_reflected_differences` and `uniform_of_rational_reflected_differences`](Green28ReversalField.lean) · [Pinned Green 28](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean)

## Reversal quotients

Let $f,g$ be the normalized nonnegative marginal polynomials with constant and leading coefficients one, and $f^*(X)=X^{\deg f}f(1/X)$. The field of the coefficients of $f$ is also the smallest real subfield $K$ over which $f^*/f$ can be written as $U/V$, with $V(0)\ne0$. The Lean statement uses the exact polynomial identity $f^*V=fU$ to allow cancellations. [`coefficients_iff_reversal`](Green28ReversalField.lean) · [Equality of the two probability fields](GREEN-28-ARITHMETIC.md)

For example, suppose $f=LR$ with $L$ rational and $R^*=cR$ for a rational $c$. Then $f^*/f=cL^*/L$ is rational, and both $f$ and $g$ have only zero or one as coefficients. The pieces $L,R$ need not be nonnegative. In particular the criterion allows $f$ itself to be nonreciprocal. [`binary_of_rational_times_reciprocal`](Green28ReversalField.lean)

## Unrestricted cyclotomic factors

Let $H$ be the shifted output mask. A reusable certificate over $\mathbb Q[X]$ is
\[
H\mid\Bigl(\prod_{j}T_j\Bigr)(X^m-1)^e,\qquad m>0,\quad e\ge0.
\]
The $T_j$ are monic. Linear factors can repeat. Each nonlinear $T_j$ is rationally irreducible, has constant term $\pm1$, and has prime degree distinct from all other nonlinear degrees in the list. There is no degree or multiplicity bound on the cyclotomic part. Under this certificate both original integer laws are uniform. [`uniform_of_cyclotomic_prime_core`](Green28PaddedFactors.lean) · [Distinct-prime subproduct theorem](GREEN-28-PRIME-FACTORS.md)

To see why the unrestricted padding works, split one monic **real** marginal polynomial into $D W$, where $D$ divides the rational core and $W$ divides the padding. All complex roots of $W$ lie on the unit circle. Reversal gives $W^*=W(0)W$ and $W(0)=\pm1$. Since the marginal has constant coefficient one, $D(0)$ is rational too. The subproduct theorem makes $D$ rational. The reversal-quotient criterion now applies to $DW$. The polynomial version permits any nonzero real padding polynomial with unit-modulus roots. [`binary_of_padded_prime_factors`](Green28PaddedFactors.lean) · [Reversal on the unit circle](Green28RootLocation.lean)

## Coefficient recovery

Put $d=\deg f$. For every $i>0$, at least one of $f^*_i,g_i$ vanishes. For $i\le d$ this follows from the coefficient of $X^d$ in $fg$, where $f_dg_0=1$ exhausts the available mass. For $i>d$ it follows from the degree. Suppose all earlier coefficients of $f,g,f^*$ belong to $K$. The coefficient of $X^i$ in $fg$ gives $f_i+g_i\in K$. If $f_i^*-f_i\in K$, then either zero coefficient suffices to put all three entries in $K$. For a reversal quotient defined over $K$, the equation $f^*V=fU$ gives this difference after division by $V(0)=U(0)\ne0$. The induction applies at every index. For the original laws the leading normalization is exactly the endpoint probability $P(a)$. [Coefficient induction and PMF transport](Green28ReversalField.lean) · [Boundary coefficient lemma](Green28RootLocation.lean)

Hasanbegović's palindromic-support criterion also exploits the coefficient at $d$. The present field statement keeps the nonzero reflected differences and both original laws. DeepMind's issue and statement PR, Left to Solve, OMA's two located reductions, the personal notebook and the cited polynomial literature were checked. The unrestricted Green 28 remains open. Lean 4.33.1 rebuilt the pinned source and nine notebook modules. All nine exact sources passed independent kernel replay, with 50 axiom reports listing exactly `propext`, `Classical.choice` and `Quot.sound`. [Hasanbegović, Theorem 3](https://arxiv.org/html/2611.14596v1) · [Hare's coefficient constraints](https://doi.org/10.1080/10586458.2025.2527786) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28) · [OMA first reduction](https://github.com/lefttosolve2/open-math-agents/pull/9606) · [OMA polynomial formulation](https://github.com/lefttosolve2/open-math-agents/pull/21793)
