# Green 28 for commensurable interior masses

Let two independent integer-valued random variables have a sum that is uniform on its support. Suppose that, within each marginal, every ratio of two positive atom masses strictly between the leftmost and rightmost atom is rational. Then both marginals are uniform. The supports can have arbitrary sizes and gaps. Each law has its own interior scale, with no prescribed ratio to the endpoint mass. Equivalently, a counterexample requires two interior atoms in at least one marginal whose masses have irrational ratio. [Lean proof](Green28InteriorRatios.lean) · [Pinned Green 28](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean)

## Why the two interior scales are related

Translate each support to start at zero and divide each probability polynomial by its endpoint mass. The resulting nonnegative monic polynomials $f,g$ have constant coefficient one and binary product. If either is binary, both are. Otherwise each has an occupied interior site. At the first occupied positive interior offset $j$ of either factor, the product coefficient is $f_j+g_j=1$. Neither summand can be one, since commensurability would then make that entire factor rational. Hence $u=f_j$ and $g_j=1-u$ both lie strictly between zero and one. For $D=\deg f$ and $E=\deg g$ the polynomials take the form
\[
 f=A+uL,\qquad g=B+(1-u)M,\qquad A=1+X^D,\quad B=1+X^E ,
\]
where $L,M$ are rational, vanish at zero and have smaller degrees than their respective endpoint polynomials. Rational $u$ gives uniformity directly. [Polynomial normalization](Green28UniformSums.lean) · [Rational-factor rigidity](Green28PolynomialReduction.lean)

## Reversal on a line of polynomials

Write $H=fg$. The identity
\[
 H-A(B+M)=u(LB-MA+LM)-u^2LM
\]
has rational polynomial coefficients. For irrational $u$, comparing a nonzero coefficient of $LM$ first gives $u^2=a u+b$ with $a,b$ rational. Comparing all coefficients then gives $LB-MA=(a-1)LM$. Put $c=a-1$. If $c=0$, then $u(u-1)=b$ is a rational algebraic integer strictly between $-1$ and $0$. Thus $c\ne0$.

Take $G=\gcd(L,M)$, $L=UG$ and $M=VG$. Cancelling $G$ and using coprimality gives $A=UP$, $B=VQ$ with $Q-P=cG$. The polynomials $P,Q$ have the same constant and leading coefficients and degree. All their roots lie on the unit circle because they divide the corresponding binomials. Each therefore reverses to itself times the common scalar $P(0)/\operatorname{lc}(P)$. At their common degree, coefficient reversal is linear. Since $G=(Q-P)/c$ has smaller degree, $P+uG$ has this same reversal scalar. Now $f=U(P+uG)$ has a rational factor times a factor reciprocal up to rational scaling, which forces both marginals to be uniform. The checked lemma `binary_of_shapes` also applies to general rational $A,B$ all of whose complex roots have modulus one. [Reversal criterion](Green28ReversalField.lean) · [Unit-root argument](Green28RootLocation.lean)

## Scope and verification

`Green28InteriorRatios.uniform_of_interior_ratios` uses the original `Green28.indepSum` and `Green28.IsUniformOnSupport` and adds one interior-ratio hypothesis for each law. Uniformity of the sum already implies finite marginal supports. The unrestricted conjecture remains open. Related work studies computational coefficient patterns, separated blocks, and a single trinomial with an arbitrary cofactor. The live DeepMind issue, statement PR, Left to Solve entry and OMA reduction head were checked for overlap. [Hare](https://arxiv.org/abs/2307.07363) · [Hasanbegović](https://arxiv.org/html/2611.14596v1) · [Trinomial theorem](https://hexagonmath.org/pdf/2611.00674v2) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28) · [OMA first reduction](https://github.com/lefttosolve2/open-math-agents/pull/9606) · [OMA polynomial reduction](https://github.com/lefttosolve2/open-math-agents/pull/21793)

Lean 4.33.1 rebuilt the pinned upstream module and seven notebook modules from source. Each notebook module passed independent kernel replay. All 45 axiom reports listed exactly `propext`, `Classical.choice` and `Quot.sound`. For focused replay from the pinned Lake environment, pass `Green28InteriorRatios` to the [notebook runner](../../scripts/replay-research).
