# Green 28 and the conjugates of a deficient weight

Suppose an independent integer sum is uniform on its support. One marginal takes at most two distinct positive probabilities, and every sum involving a lighter atom of that marginal has at most two ordered representations. If the lighter-to-heavier probability ratio is totally real, **both marginals are uniform**. This holds in every algebraic degree. The opposite marginal can have arbitrary support and masses. [Fairness theorem](Green28ConjugateSignature.lean) · [Double representations](GREEN-28-DOUBLE-FIBRES.md)

More precisely, in any counterexample let $r,c$ count the real and nonreal complex roots, respectively, of the monic minimal polynomial of the deficient ratio $u$. Then $r<128c$. Thus more than $1/129$ of its conjugates are nonreal. Each member of a complex-conjugate pair counts separately. The parameter is an algebraic integer, so its characteristic-zero minimal polynomial has simple roots. The Lean statement counts roots with multiplicity. [Quantitative obstruction](Green28ConjugateSignature.lean)

## An integer polynomial on the allowed interval

The double-representation theorem gives $1/2<u<1$ and bounds every conjugate $z$ by $|z|\le2$ and $(|z|-1)|1-z|\le1$. A real conjugate $x<-1$ therefore has $x^2\le2$. All real conjugates belong to $[-91/64,2]$. Consider
\[
  T(x)=x(x-1)(x-2)(x+1)^2(x^2-2)(x^2-x-1)(x^3-x^2-2x+1).
\]
Its factors are nonzero for $1/2<x<1$. On $[-91/64,2]$ it satisfies $|T(x)|\le29/32$. The proof checks eleven intervals whose endpoints, multiplied by 64, are
\[
 -91,-64,-37,-10,18,45,73,100,114,121,124,128.
\]
For consecutive endpoints $a,b$, write $x=(a+bt)/(64(1+t))$ with $t\ge0$. After clearing the positive denominator, both $29+32T(x)$ and $29-32T(x)$ have polynomials in $t$ with nonnegative coefficients. Lean checks each expanded polynomial. At the final endpoint $T(2)=0$. For complex $z$ with $|z|\le2$, Horner evaluation and the triangle inequality give $|T(z)|\le35760<2^{16}$. [Exact polynomial certificates](Green28ConjugateSignature.lean)

## The integer norm

The resultant of the monic integral minimal polynomial of $u$ and $T$ is a nonzero integer. Its absolute value equals the product of $|T(z)|$ over the conjugates. Hence
\[
  1\ \le\ (29/32)^r (2^{16})^c .
\]
Since $(29/32)^{128}2^{16}<1$, the displayed inequality contradicts $r\ge128c$ when $c>0$. When $c=0$, the positive degree gives $r>0$ and the right-hand side is less than one. The reusable declaration `one_le_conjugate_product` applies to any integer polynomial nonvanishing at an algebraic integer. The numerical proportion is a proved lower bound. [Resultant and count](Green28ConjugateSignature.lean)

## Sources and scope

This uses the classical integer-polynomial method of bounding conjugates by a nonzero resultant. Integer Chebyshev polynomials and the classification of totally real algebraic integers with all conjugates in $[-2,2]$ give related context. Here the quantitative result allows nonreal conjugates as well. [Borwein and Erdélyi, *The integer Chebyshev problem*](https://people.tamu.edu/~terdelyi/papers-online/ICP.pdf) · [Totally real algebraic integers and Kronecker's theorem](https://pmc.ncbi.nlm.nih.gov/articles/PMC12107117/)

The probability results use `Green28.indepSum` and `Green28.IsUniformOnSupport`. Uniformity of the sum supplies both finite-support hypotheses of the pinned declaration. Its unrestricted conclusion remains open. The DeepMind issue and statement PR, Left to Solve and the OMA reductions were checked. The two-site OMA result bounds the number of support points. Ghidelli's recurrence and the trinomial manuscript concern specified support patterns. These searches found no matching conjugate-proportion theorem. [Pinned problem](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28) · [OMA R1](https://github.com/lefttosolve2/open-math-agents/pull/9606) · [OMA R2](https://github.com/lefttosolve2/open-math-agents/pull/21793) · [OMA two-site reduction](https://github.com/lefttosolve2/open-math-agents/pull/27234) · [Ghidelli](https://arxiv.org/abs/2209.09843) · [Trinomial manuscript](https://hexagonmath.org/pdf/2611.00674v2)

The clean Lean 4.33.1 build and independent kernel replay covered all thirteen notebook modules in the source closure. All 86 printed axiom reports list only `propext`, `Classical.choice` and `Quot.sound`. Use `Green28ConjugateSignature` with the notebook runner in the pinned Lake environment. [Replay runner](../../scripts/replay-research)
