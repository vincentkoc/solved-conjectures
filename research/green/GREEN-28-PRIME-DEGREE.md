# Green 28 with an irreducible output mask of prime degree

Let $S$ be the finite support of an exactly uniform independent sum of two integer laws. Write $H_S(X)=\sum_{s\in S}X^{s-\min S}$. If its degree is prime and $H_S$ is irreducible over $\mathbb Q$, **one summand is constant**. Both original marginals are then uniform on their supports. The probabilities may be arbitrary real numbers. [Point-mass and uniformity theorems](Green28PrimeDegree.lean) · [Pinned Green 28](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean)

For example, take $S=\{0,1,3,5\}$. Its mask $H=X^5+X^3+X+1$ vanishes at one modulo two. Over $\mathbb F_3$, division of $X^9-X$ by $H$ leaves $D=2X^4+X^3+X^2+2X$, and division of $H$ by $D$ leaves one. Hence $H$ has no irreducible factor of degree one or two modulo three. A reducible quintic must have such a factor. This proves rational irreducibility and gives a concrete application beyond the primitive binary criterion. The numerical example is a hand calculation. [Primitive binary criterion](GREEN-28-PRIMITIVE-SUPPORT.md)

## Conjugate products

The algebraic theorem allows any monic $H\in\mathbb Q[X]$ irreducible of prime degree $p$, and arbitrary monic complex factors $H=fg$. If $f(0)=1$, one factor has degree zero. Drmota and Skałba's theorem on nontrivial multiplicative relations between conjugates of odd prime degree provides a classical antecedent. The Lean proof establishes the subset-product obstruction directly, including degree two. [Drmota and Skałba, *On multiplicative and linear independence of polynomial roots* (1991), Theorem 1, stated in Virbalas, Lemma 8](https://doi.org/10.3390/math11061485)

The Galois group contains an element acting as a full cycle on the $p$ roots. Write them $a_i$ in cyclic order in a complex embedding of the splitting field. A nonconstant proper factor selects a subset $I$ with $0<|I|<p$. Its unit constant term gives $\prod_{i\in I}(-a_i)=1$. Transporting this identity around the cycle and taking logarithms of absolute values gives $\sum_{i\in I}u_{n+i}=0$, where $u_i=\log|a_i|$.

The polynomial $F=\sum_{i\in I}X^i$ is coprime to $X^p-1$ over $\mathbb Q$. Indeed $F(1)=|I|$ is positive, and divisibility by the monic cyclotomic factor $\Phi_p$ would imply $p\mid F(1)$ already over the integers. Apply Bézout's identity to the shift on the periodic sequence $u$. It gives $u=0$, so every root has modulus one. Odd degree gives a real root, which would be $1$ or $-1$, contradicting rational irreducibility. In degree two the chosen subset has one member and the constant-term condition forces that root to be $-1$ directly. [Polynomial and Galois proof](Green28PrimeDegree.lean)

For the probability theorem, normalize the two marginal generating polynomials to monic real polynomials. They have unit constant coefficients and multiply to the actual shifted mask. A degree-zero marginal polynomial describes a point mass. The same normalization is now shared with the primitive-mask theorem. [Mask and probability bridge](Green28PrimitiveSupport.lean)

## Scope and replay

DeepMind's issue and statement PR, Left to Solve, both located Open Math Agents reductions, the personal notebook, and the prime-degree conjugate-product literature were checked. No matching Green 28 formalization was located. The unrestricted problem remains open. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28) · [OMA first reduction](https://github.com/lefttosolve2/open-math-agents/pull/9606) · [OMA polynomial version](https://github.com/lefttosolve2/open-math-agents/pull/21793) · [Unfair polynomial formulation](https://arxiv.org/abs/2209.09843)

Lean 4.33.1 rebuilt the pinned declaration and five notebook modules from clean sources. Each notebook module passed independent kernel replay. The 27 axiom reports across the closure each contain exactly `propext`, `Classical.choice` and `Quot.sound`.
