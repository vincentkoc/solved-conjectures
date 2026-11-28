# Green 28 with an approximately uniform sum

For every $\varepsilon>0$ there are independent integer laws $P,Q$ with the following properties. All three supports are finite intervals. Each marginal has at most two distinct positive probabilities, all rational. Each has total variation distance greater than $1-\varepsilon$ from the uniform law on its own support. Yet at **every** occupied output $z$, the sum probability has relative error less than $\varepsilon$ from uniform. If the output interval has $M$ sites, the asserted error is $|M\Pr[X+Y=z]-1|$. [Theorem and finite certificate](Green28NearInterval.lean)

## A family with explicit errors

Fix an integer $n\ge2$. Start with the sets
\[
 A=\{0,n,\ldots,n(n-1)\},\qquad
 B=\{0,\ldots,n-1\}\ \cup\ \{n^2,\ldots,n^2+n-1\}.
\]
Their independent uniforms sum to the uniform law on $[0,2n^2)$ in the integers. Every output has exactly one representation. Its middle base-$n$ digit gives the index in $A$. The low digit and the choice of lower or upper block give the site in $B$. This is an instance of the classical direct-sum decomposition of an integer interval. [Zhigljavsky, Golyandina and Gryaznov, *Deconvolution of a discrete uniform distribution*](https://doi.org/10.1016/j.spl.2016.06.006)

Let $I,J$ be the full integer intervals between the endpoints of $A,B$. Put $t=n^{-4}$. Mix the uniform on $A$ with weight $t$ of the uniform on $I$, giving the old law weight $1-t$. Make the corresponding mixture on $B,J$. For a set of $s$ sites inside an interval of $d$ sites, this mixture has distance $(1-t)(1-s/d)$ from the uniform on the interval. In the two marginals the exact distances are therefore
\[
 (1-t)\left(1-\frac{n}{n(n-1)+1}\right),\qquad
 (1-t)\left(1-\frac{2n}{n^2+n}\right).
\]
Both tend to one. For each occupied output the two replacements change its probability by at most $2t$. Its original probability was $1/(2n^2)$, so the relative error is at most $4/n^2$. The sum support stays exactly $[0,2n^2)$ because the endpoints stay fixed and all original representations remain occupied. [Mixture estimate and construction](Green28NearInterval.lean)

## Relation to the exact problem

The pinned Green 28 question assumes exact equality of all occupied sum probabilities. The earlier variation-gap equivalence also has that hypothesis. Here the sum is compared with the uniform law on its full support using a pointwise relative error. Consequently, allowing any fixed positive error cannot give a uniform gap below distance one, even for interval supports and two rational weights per input. With exact uniformity, rational probability ratios on either marginal already force fairness. [Pinned Green 28](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean) · [Variation gap](GREEN-28-VARIATION-GAP.md) · [Rational ratios](GREEN-28-ARITHMETIC.md)

DeepMind’s tracking issue and statement PR, Left to Solve, the two located Open Math Agents reductions, and the unfair-dice and interval-deconvolution literature were checked. These sources treat exact factorization. The searches found no matching formalized pointwise approximation counterexample. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28) · [OMA first reduction](https://github.com/lefttosolve2/open-math-agents/pull/9606) · [OMA polynomial comparison](https://github.com/lefttosolve2/open-math-agents/pull/21793) · [Ghidelli](https://arxiv.org/abs/2209.09843)

Lean 4.33.1 rebuilt the pinned declaration and all eleven notebook modules in the dependency closure from clean sources. Each notebook module passed independent kernel replay. The three axiom reports in the new file contain exactly `propext`, `Classical.choice` and `Quot.sound`.
