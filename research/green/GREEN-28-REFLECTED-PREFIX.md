# Green 28 from the outer quarters of the sum support

Suppose the sum of two independent integer random variables is uniform on a finite nonempty set $S$. Put $a=\min S$, $b=\max S$ and $N=b-a$. If
\[
   a+i\in S \quad\Longleftrightarrow\quad b-i\in S
   \qquad (0\le i<\lfloor N/4\rfloor),
\]
then **both original laws are uniform**. The two end patterns can have arbitrary gaps and the middle can be asymmetric. The declaration takes an integer cutoff $t\ge0$, the membership equivalence for $i<t$ and $N\le4t+3$. Taking $t=\lfloor N/4\rfloor$ gives the displayed test. [Lean theorem](Green28ReflectedPrefix.lean) · [Pinned Green 28 predicate and conclusion](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean)

For example, take $t\ge2$ and
\[
   S=\{0,1,t+1,t+2,4t+2,4t+3\}.
\]
The outer offsets match, while $t+1$ lacks its reflection. The set occurs as a sum of two nonconstant uniform laws on $\{0,1\}$ and $\{0,t+1,4t+2\}$, with each total represented once. The theorem applies to every independent decomposition with that uniform sum law.

## Reflection at the first differing coefficient

Let $f,g$ be the normalized monic nonnegative marginal polynomials, both with constant coefficient one, and let $f^*$ denote reversal. For every cutoff $t$, the product $fg$ and its reversal agree below $t$ **if and only if** both $f,f^*$ and $g,g^*$ do. In particular the first mismatch from the ends of the output occurs at the first mismatch in either marginal. [`matches_mul_iff`](Green28ReflectedPrefix.lean)

Suppose the two marginal pairs already agree below index $i$. At $i$ the difference for the product is $(f_i-f^*_i)+(g_i-g^*_i)$ because all interior terms in the convolution agree. For $i>0$ the coefficient at degree $\deg f$ already contains the unit contribution $f_{\deg f}g_0$. Thus $f_i^*g_i=0$. Exchanging the factors gives $g_i^*f_i=0$. These two restrictions and nonnegativity force the individual differences to vanish whenever their sum is zero. Induction gives the equivalence for every prefix. [Boundary coefficient lemma](Green28RootLocation.lean)

If one marginal has degree at most $2t$, the matching prefix makes that entire polynomial reciprocal. Hasanbegović's palindromic-support criterion then gives fairness. Otherwise both degrees are at least $2t+1$. Since they sum to $N\le4t+3$, each is at most $2t+2$. In a factor of degree $d$ with this bound, any unpaired support site and its missing reflection have offsets at least $t$ from either end. They are distinct, so one has offset $t$ and the other $d-t$. At most one occupied site can lack its reflection. Applying the earlier one-unpaired-site theorem to both original supports gives fairness here too. [Short-factor theorem](Green28ReflectedPrefix.lean) · [One unpaired site in each marginal](GREEN-28-UNPAIRED-SITES.md)

## Scope and attribution

Krasner and Ranulac proved fairness for a consecutive interval. Ghidelli records the extension of their argument to a fully palindromic output. Hasanbegović treats a palindromic marginal support against an unrestricted partner. The result above localizes the reflection argument to a prefix of the output and certifies the quarter-width criterion on the actual integer sites. The unrestricted Green 28 remains open. [Ghidelli, §1](https://arxiv.org/pdf/2209.09843) · [Hasanbegović, §3](https://arxiv.org/html/2611.14596v1)

DeepMind's issue and merged statement, Left to Solve, OMA's two reductions, the personal notebook and the cited sources were checked. Lean 4.33.1 rebuilt the pinned source and seven notebook modules. Each notebook module passed independent kernel replay. The 40 axiom reports list exactly `propext`, `Classical.choice` and `Quot.sound`. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [DeepMind statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28) · [OMA first reduction](https://github.com/lefttosolve2/open-math-agents/pull/9606) · [OMA polynomial reduction](https://github.com/lefttosolve2/open-math-agents/pull/21793)
