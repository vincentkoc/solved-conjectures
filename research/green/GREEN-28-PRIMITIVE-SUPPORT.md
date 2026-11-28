# Green 28 with a primitive output support

For a nonempty finite set $S$ of integers, shift its minimum to zero and form the integer polynomial
\[
 H_S(X)=\sum_{s\in S} X^{s-\min S}.
\]
If its reduction modulo two is **primitive**, every decomposition of the uniform law on $S$ as a sum of two independent integer variables has a **constant summand**. In particular, both marginals are uniform on their respective supports. The theorem allows arbitrary real marginal probabilities. Primitive supports exist at every positive width. [Point-mass theorem, fairness and existence](Green28PrimitiveSupport.lean) · [Pinned Green 28](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean)

Here primitivity has its finite-field meaning. For $d=\deg H_S>0$, the test asks whether the reduction has a root $\alpha$ of multiplicative order $2^d-1$ in $\mathbb F_{2^d}$. This is a condition solely on the output support. For example, the support $\{0,1,3\}$ gives $1+X+X^3$. Its cubic reduction has no binary root, so it is irreducible. Its roots in $\mathbb F_8$ differ from one, hence have order seven. The test applies to every translate of this support. [Definition and finite-field background, Brent and Zimmermann, §1](https://maths-people.anu.edu.au/~brent/pd/rpb212.pdf)

## The obstruction

Normalize the marginal generating polynomials to monic real factors $f,g$ of $H_S$. Their constant terms equal one. Their coefficients are algebraic integers because the factors are monic divisors of a monic integer polynomial. Take a maximal ideal of the real algebraic integers lying over two. Reduction there preserves both degrees, the product, and the constant terms. The proof works in an algebraic closure of the residue field. [Normalization and coefficient integrality](Green28UniformSums.lean) · [Integral specialization](Green28PrimitiveSupport.lean)

For $d\ge2$, the $d$ distinct roots of the reduced mask are $\alpha^{2^i}$ for $0\le i<d$. A monic factor selects a subset $I$ of these roots. In characteristic two, its constant term is their product, $\alpha^{\sum_{i\in I}2^i}$. If $I$ is nonempty and proper, its exponent is strictly between zero and $2^d-1$. The product therefore cannot be one. The degree-one case follows directly from the degree sum. The algebraic theorem allows arbitrary signs among the other coefficients of the real factors. It suffices for one factor to have constant term one. [Orbit obstruction and real factorization](Green28PrimitiveSupport.lean)

Conversely, to exhibit eligible supports of any width $d>0$, choose a multiplicative generator in $\mathbb F_{2^d}$ and multiply the linear factors over its Frobenius orbit. Squaring permutes the factors, so every coefficient is zero or one. The support of this polynomial gives the required integer mask, with constant and leading coefficients one. This uses the classical existence of primitive polynomials over finite fields. Green 28 enters in the application to independent integer sums. [All-width construction](Green28PrimitiveSupport.lean)

## Scope and verification

Ghidelli and Hare study the unfair binary polynomial question in terms of its nonnegative real factors. The DeepMind issue and statement PR, Left to Solve, the current Open Math Agents reductions, and literature searches for primitive support polynomials were checked. No matching formalized point-mass criterion was found. The unrestricted conjecture remains open. [Ghidelli](https://arxiv.org/abs/2209.09843) · [Hare](https://arxiv.org/abs/2307.07363) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28) · [OMA first reduction](https://github.com/lefttosolve2/open-math-agents/pull/9606) · [OMA polynomial comparison](https://github.com/lefttosolve2/open-math-agents/pull/21793)

Lean 4.33.1 rebuilt the pinned declaration and all four notebook modules in the dependency closure from clean sources. Each module passed independent kernel replay. The five new axiom reports each list exactly `propext`, `Classical.choice` and `Quot.sound`.
