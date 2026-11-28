# Sharp common support from quartic characters

Let $b(p)$ be the smallest size of a common set of labels for two independent real probability laws on $\mathbb Z/p\mathbb Z$ whose sum is exactly uniform. The inputs can have different laws. For a prime $p\equiv1\pmod8$, write $p=a^2+b^2$ with $a\equiv3\pmod4$. The odd coordinate has a unique sign under this convention. If $a\ge-1$, then $b(p)=(p+1)/2$. The common labels are zero and the nonzero quadratic residues. The lower bound applies to all common label sets and all real input laws. [Arithmetic criterion and minimum](Green33QuarticJacobi.lean) · [Prime lower bound](PRIME-QUOTIENT-FLATNESS.md)

| Prime | Signed coordinate | Consequence |
| --- | --- | --- |
| $17=(-1)^2+4^2$ | $-1$ | The minimum is nine. |
| $73=3^2+8^2$ | $3$ | The minimum is 37. |
| $41=(-5)^2+4^2$ | $-5$ | The opposite quartic weights below fail. Other support sets and laws are possible candidates. |

## The sign test

Let $q$ indicate the nonzero squares. Let $s$ equal $1$ on nonzero fourth powers, $-1$ on the other nonzero squares, and zero elsewhere. Start with the two masses

\[
 w_\pm=c\delta_0+\tfrac12(q\pm r s),\qquad c>0,\quad 0<r<1.
\]

Each is positive at every common label. Set $K=2(s*s)(1)+1$, with convolution taken in the additive group. For a quartic multiplicative character $\chi$, the proof identifies $K$ with the real part of $J(\chi,\chi)$. The Jacobi sum has Gaussian integer coordinates and squared norm $p$. Reducing the signed row modulo two gives $K\equiv3\pmod4$. Uniqueness of the odd coordinate with that residue gives $K=a$. These are classical order-four cyclotomic evaluations. Ding records the cyclotomic numbers in Table I. [Ding, *Two Constructions of Difference Families*](https://cse.hkust.edu.hk/faculty/cding/JOURNALS/jcd081.pdf) · [Jacobi-sum proof](Green33QuarticJacobi.lean)

Comparing the convolution at zero, a nonzero square, and a nonsquare gives

\[
 4c=1+K r^2,\qquad
 8c^2-4c+(p+1)/2=p r^2.
\]

Since $K^2<p$, take $r^2=(1+\sqrt{1-K^2/p})^{-1}$. Positive central mass exists exactly when $K\ge-1$. Normalizing the two masses gives independent draws with sum probability $1/p$ at every residue. The converse sign test concerns the displayed pair of weights. [Weight equations and converse](Green33QuarticReal.lean) · [Normalization into probability laws](Green33RealBudget.lean) · [Sherstnev on decompositions of the uniform distribution](https://doi.org/10.1137/S0040585X97979937)

## Relation to Green 33

The pinned question asks for infinitely many ordinary cyclic bases of size $(\sqrt2+o(1))\sqrt p$, allowing composite orders. The result here treats exact uniformity with independent real weights on a common set of size linear in a prime order. The prior notebook bounds $b(p)$ within two of $(p+1)/2$ at every odd prime and gives the value on primes congruent to three modulo four. The quartic criterion attains the lower endpoint on its stated arithmetic class. [Canonical Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Earlier prime bounds](REAL-PRIME-BUDGET.md) · [Approximate weighted equivalence](WEIGHTED-STABILITY.md)

The source issue closed with the formalization. Left to Solve has no linked solution. Targeted searches in DeepMind, Open Math Agents and this notebook found no matching Lean contribution. [Source issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Formalization PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33) · [Open Math Agents search](https://github.com/lefttosolve2/open-math-agents/issues?q=%22quartic%22+%22uniform+convolution%22)

Replay **Green33QuarticJacobi** with the [notebook runner](../../scripts/replay-research). Ten notebook modules underwent fresh elaboration and independent kernel replay. All 69 printed axiom sets are subsets of the standard three.
