# Green 28 for a uniform sum on eleven integers

The uniform law on **any eleven distinct integers** has a constant summand in every decomposition into independent integer laws. More generally, a uniform sum on at most eleven sites has uniform marginals. A counterexample to Green 28 would require at least six more output sites than the cardinality of its larger marginal. These are statements about the original PMFs with unrestricted gaps. [Lean statements and proofs](Green28OutputBoundary.lean) · [Pinned Green 28](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean)

## Equality in the previous count

Translate the marginal supports $A,B$ to minimum zero and write $D=\max A$, $E=\max B$. Suppose $B$ is the larger support by cardinality and the uniform output set $S$ has at most $|B|+5$ elements. If the laws fail to be uniform, then $|B|\ge6$ by the five-site theorem. The earlier bound in terms of the numbers $h,k$ of maximal-mass sites forces $h=k=2$. These are precisely the endpoints on each side. Their four pairs give four distinct uniquely represented totals. [Weighted output count](GREEN-28-OUTPUT-CARDINALITY.md) · [Five-site theorem](GREEN-28-ISOLATED-TABLES.md)

The first deficient sites have the same offset $r>0$ from the left ends. The last deficient sites are $D-s,E-s$, at the same offset from the right ends. All $|B|$ values in $r+B$ have multiple representations, as does $D+r$. The latter is outside $r+B$ because $D\in B$ would give the endpoint total $D$ two representations. Hence $D+r$ is the only multiply represented total outside $r+B$.

If $D-s>r$, then $(D-s)+E$ lies beyond $r+B$ and must equal $D+r$. This gives $E-s=r$, so $B$ has a single deficient site. With its two maximal sites it would have at most three elements. Thus $D-s=r$ and $A=\{0,r,D\}$. The low-column total $E-s$ also lies outside $r+B$, since $E-D\in B$ would give two representations of the endpoint total $E$. Therefore $E-s=D+r$, which gives $E=2D$. [Finite-set equality argument](Green28OutputBoundary.lean)

## Three coefficients of a trinomial product

Write the normalized marginal on $A$ as $f=1+uX^r+X^D$, with $0<r<D$. Let the partner polynomial $g$ have arbitrary nonnegative coefficients, constant and leading coefficients one, and degree at most $2D$. Write $H=fg$ for the binary output polynomial. The unit contribution at degree $D$ forces $g_D=0$. Expanding the product at just three indices gives
\[
    H_r-H_{D+r}+H_{2D+r}=u(1+g_{2D}).
\]
The left side is an integer. The coefficient $g_{2D}$ is either zero or the leading coefficient one. Hence $u$ is rational, and rational-factor rigidity gives binary coefficients for both marginals. This excludes the equality configuration above. The same three-coefficient argument proves the stated double-width criterion for any marginal with at most three atoms. A separate manuscript gives the arbitrary-width trinomial theorem. [Checked double-width criterion](Green28OutputBoundary.lean) · [Trinomial manuscript, Theorem 1](https://hexagonmath.org/pdf/2611.00674v2) · [Rational-factor proof](Green28PolynomialReduction.lean)

Consequently any failure requires $|S|\ge\max(|A|,|B|)+6$. If $|S|\le11$, both marginal supports would have at most five sites, which gives fairness. For uniform marginals with a uniform sum, every pair gives a distinct total and $|S|=|A||B|$. Since eleven is prime, a support has size one. The general conjecture remains open. [Prime-size constant-summand conclusion](Green28OutputBoundary.lean)

## Sources and verification

The live search covered the DeepMind issue and statement PR, Left to Solve, OMA's two reductions, the notebook and the related polynomial literature. Lean 4.33.1 rebuilt the pinned declaration and eleven local modules in a clean directory. Each local module passed independent kernel replay. All 57 axiom reports list exactly `propext`, `Classical.choice` and `Quot.sound`. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28) · [OMA first reduction](https://github.com/lefttosolve2/open-math-agents/pull/9606) · [OMA polynomial reduction](https://github.com/lefttosolve2/open-math-agents/pull/21793) · [Hasanbegović on aligned coefficients](https://arxiv.org/html/2611.14596v1)
