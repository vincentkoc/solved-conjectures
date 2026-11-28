# Green 28 · Inverse stability for a uniform integer sum

Fix a budget of $k$ outcomes and a marginal error $\varepsilon>0$. There is a $\delta>0$ such that whenever the independent sum of two integer laws $P,Q$ is within $\delta$ in total variation of the uniform law on a nonempty set $S$ with $|S|\le k$, there are integer laws $U,V$ with
$$
U*V=\operatorname{Unif}(S),\qquad d_{\rm TV}(P,U)\le\varepsilon,\qquad d_{\rm TV}(Q,V)\le\varepsilon .
$$
Both corrections use the **original integer sites**. The same tolerance works for every spacing of the target and for input laws of infinite support. There is also a radius $\rho_k>0$ such that, after choosing $\delta$ for $\min(\rho_k,\varepsilon)$, exactly one ordered exact pair lies within that distance of the two inputs. Other factorizations of the same target can occur farther away. [Repair and local uniqueness](Green28InverseStability.lean)

## Recovering an exact pair

If the sum puts mass greater than $1-2\delta$ on $S$, averaging over one input gives a translate of $S$ carrying more than $1-2\delta$ of the other. Choose one such set of sites for each input and number its entries. For $m=|S|$ the only addition data needed on these two lists are the $m^2$ labels recording which target site a pair hits, or whether it misses $S$. There are finitely many such patterns, independent of diameter. [Concentration and finite patterns](Green28InverseStability.lean)

For each pattern the two weight vectors lie in the compact cube $[0,1]^{2m}$. The constraints demand unit row totals, zero product on pairs missing $S$, and at most $1/m$ in each target cell. At zero error the cell masses sum to one, so every cell has mass exactly $1/m$. Compactness puts sufficiently accurate approximate weights close to exact weights. Taking the minimum over the finitely many patterns and sizes gives the uniform tolerance. If two vectors on $m$ sites differ by at most $t$ per site from the corresponding masses of the original laws, a normalized corrected law differs from its original by at most $mt$ in total variation. The event estimate includes the original tails. [Finite repair and transfer to the original PMFs](Green28InverseStability.lean)

## Why the nearby pair is unique

All atom probabilities of an exact factor belong to a finite set $A_k$. Choose $2\rho_k$ smaller than every positive gap between entries. If two candidate factors are each within $\rho_k$ of the same input, their probabilities on each singleton differ by at most $2\rho_k$. They therefore agree on every integer. This also separates distinct possible marginals arising from **different** uniform targets within the budget. [Separation theorem](Green28InverseStability.lean) · [Finite mass spectrum](GREEN-28-MASS-SPECTRUM.md)

## Relation to Green 28

`Green28InverseStability.green_28_iff_robust` identifies the literal pinned conjecture with the assertion that the simultaneous exact repairs can always be chosen uniform on their respective supports. In the forward direction the repaired laws have finite support because their sum has finite support. Conversely, apply the robust assertion to an already exact input pair with an error below the separation gap. Each fair approximation then equals its corresponding input. The unconditional repair theorem gives existence and local uniqueness. The fairness of an arbitrary exact factor and numerical values of the tolerances remain open here. [Formal equivalence](Green28InverseStability.lean) · [Pinned declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean)

Zhigljavsky, Golyandina and Gryaznov classify exact factorizations of a uniform law on an integer interval. Bausch and Cubitt study finite-distribution decomposability and weak-membership formulations. The earlier notebook example has growing output support and compares each input to the uniform law on its own full support. Here the nearby factors may have different supports from the input laws. [Exact interval factorizations](https://doi.org/10.1016/j.spl.2016.06.006) · [Bausch and Cubitt](https://pmc.ncbi.nlm.nih.gov/articles/PMC5465997/) · [Earlier approximate-interval example](GREEN-28-NEAR-UNIFORM-INTERVAL.md)

Live duplicate checks covered the DeepMind issue and statement PR, Left to Solve, the OMA reductions and special cases, and the personal notebook. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28) · [First OMA reduction](https://github.com/lefttosolve2/open-math-agents/pull/9606) · [Second OMA reduction](https://github.com/lefttosolve2/open-math-agents/pull/21793) · [Two-site case](https://github.com/lefttosolve2/open-math-agents/pull/27234) · [Degree-five case](https://github.com/lefttosolve2/open-math-agents/pull/29600)

A fresh build from the pinned source and independent Lean 4.33.1 kernel replay checked all ten notebook modules. All 81 axiom reports listed only `propext`, `Classical.choice` and `Quot.sound`. Replay `Green28InverseStability` with the [notebook runner](../../scripts/replay-research).
