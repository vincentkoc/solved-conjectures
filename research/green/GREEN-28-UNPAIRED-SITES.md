# Green 28 with reflected marginal supports

Reflect a finite integer support through its midpoint, sending $x$ to $\min A+\max A-x$. Call an occupied site *unpaired* when its reflection is absent. If the independent sum of two integer laws is uniform on its support, and **each marginal support has at most one unpaired site**, both laws are uniform. Support sizes, widths, gaps and positive probabilities are unrestricted. The criterion concerns the two marginal supports. [`uniform_of_one_unpaired_each`](Green28UnpairedSites.lean) · [Pinned Green 28](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean)

## What any counterexample must look like

Write $[a,A]$ and $[b,B]$ for the extreme occupied sites of the left and right laws. Both end sites on each side have maximal mass. If the marginals fail to be uniform, let $x_-,x_+$ and $y_-,y_+$ be the extreme occupied sites **below** maximal mass on each side. They obey
\[
  x_- - a = y_- - b,\qquad A-x_+ = B-y_+ .
\]
All four listed sites lack their reflected partners in their own supports. The first and last may coincide on a given side. The theorem constructs these sites for the original probability mass functions. Uniformity of the sum supplies the needed finiteness. [`Alignment` and `alignment_alternative`](Green28UnpairedSites.lean)

For the first identity, start with the cell $(x_-,b)$. A cell is the unique representation of its sum exactly when both marginal masses there are maximal. Since this cell has another representation, write $x_-+b=x+y$ with $x<x_-$ and $y>b$. The row $x$ is maximal, so the column $y$ must be deficient. Thus $x_- -a\ge y_- -b$. Starting from $(a,y_-)$ gives the reverse inequality. At the upper endpoints the same comparison in reverse order gives the second identity. Now $(A,b)$ is a unique representation. If $a+A-x_-$ were occupied, it would pair with $y_-$ to give a second representation of $A+b$. The other three exclusions follow from the two cross-corner sums. [Proof from ordered sums and positive masses](Green28UnpairedSites.lean)

## One support against an unrestricted partner

If only the left support has at most one unpaired site, the first and last deficient sites on the left must coincide. Denote that unique site by $x$, and write $D=A-a$, $E=B-b$. In a nonuniform example the right support would have two distinct unpaired sites at $y_-=b+(x-a)$ and $y_+=B-(A-x)$, with
\[
  y_+ - y_- = E-D>0 .
\]
If $u=P(x)/P(A)$ and $d=[\mathbb Q(u):\mathbb Q]$, then $0<u<1$, $d\ge2$, $(d-1)D\le E$, and $Q$ takes at least $d$ distinct positive probability values. These last inequalities apply the previously verified one-deficient-atom theorem after deriving its mass hypothesis from the support shape. A second support with at most one unpaired site rules out the two distinct right sites. [`one_unpaired_alternative`](Green28UnpairedSites.lean) · [Algebraic degree and width](GREEN-28-ALGEBRAIC-WIDTH.md)

For example, each support may start with an arbitrary finite symmetric set of integers, keep its two endpoints, and delete one noncentral interior site. The remaining partner of that site is the sole unpaired site. The conclusion allows the two initial sets, the deleted sites and the marginal weights to be chosen independently.

## Attribution and verification

Hasanbegović's Theorem 3 establishes fairness if one factor has exactly palindromic support, even with an unrestricted other factor. Lemmas 2–3 there locate the first aligned nonbinary coefficients. The result above uses the extreme deficient sites from both ends to handle one reflection failure on each support and to constrain the unrestricted partner of a single such support. Ghidelli also describes the classical palindromic **product** case, which concerns the sum law. [Hasanbegović, §§2–3](https://arxiv.org/html/2611.14596v1) · [Ghidelli, §1](https://arxiv.org/abs/2209.09843)

DeepMind's issue and statement PR, Left to Solve and the current Open Math Agents reductions were checked. The OMA reflection comparison imposes a condition on coefficients of the product. The searches found no matching two-marginal result allowing one unpaired site per support. The unrestricted conjecture remains open. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28) · [OMA degree and reflection reduction](https://github.com/lefttosolve2/open-math-agents/pull/21793)

Lean 4.33.1 rebuilt the pinned declaration and all four local modules from clean sources. Independent kernel replay covered each local module. All four axiom reports in the new file contain exactly `propext`, `Classical.choice` and `Quot.sound`.
