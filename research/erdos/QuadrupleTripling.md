# Tripling Steiner quadruple systems

Hanani's tripling construction sends a Steiner quadruple system on $v$ points to one on $3v-2$ points. The declaration `exists_tripling` takes $v\ge3$ and an actual `H.IsBlockDesign 3 4` on `Fin v` and returns the same predicate on `Fin (3*v-2)`. Starting with the binary system of order eight gives every order $7\cdot3^d+1$ for $d\ge0$. [Lean proof](Erdos722QuadrupleTripling.lean) · [Hanani, *On Quadruple Systems* (1960)](https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/on-quadruple-systems/8D49E48326D901FD18771AD9F9B4F7E1)

## How the blocks fit together

Fix one base point $\infty$. Keep it and replace each other point by a column labelled by $\mathbf F_3$. A base block avoiding $\infty$ contributes all transversals whose four labels sum to zero. Three different columns in such a block uniquely determine the missing column and its label.

A base block through $\infty$ has three finite columns. Fill these nine points and $\infty$ with the harmonic system on the projective line over $\mathbf F_9$. To label it, identify $\mathbf F_3^2$ linearly with $\mathbf F_9$. For each fixed first coordinate, the three points in its column sum to zero, so they form a harmonic block with $\infty$. Thus every such ten-point filling contains the same four-set above a shared column, whichever linear labelling the filling uses. [Harmonic construction](HarmonicQuadruples.md)

Project a lifted triple to the original point set. If the image has size three, the original design determines the unique base block. For a smaller image, adjoin $\infty$. When this gives three points, their unique base block supplies the completion. Otherwise the triple lies in one four-point column including $\infty$. Every incident local filling completes it to that same four-set. This establishes the uniqueness clause of the pinned design predicate.

## Orders outside the earlier product families

For $d=5t+1$, each $7\cdot3^d+1$ is divisible by 11, because $3^5\equiv1\pmod{11}$. The powers of three modulo 11 run through $1,3,9,5,4$. Consequently 11 divides neither a binary order $2^e$ nor a ternary projective order $3^e+1$, nor any finite product of them. The first separated order is 22. The declaration `cofinal_outside_product_closure` gives an actual design outside the entire multiplicative closure above every cutoff. [Binary seed](Erdos722BinaryQuadruples.lean) · [Earlier product closure](QuadrupleProduct.md)

The upstream theorem asks for every sufficiently large admissible order for every $1\le r<k$. This proof supplies explicit orders for $r=3,k=4$. Hanani proved the full quadruple-system spectrum, and Keevash proved the general existence theorem. The contribution here is the Lean construction, its gluing proof and the separation from the notebook's earlier families. [Pinned Erdős 722](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/722.lean) · [Keevash](https://arxiv.org/abs/1401.3665)

## Verification and overlap

The six public results in `Erdos722.Tripling` are `glue`, `ten_point_template`, `exists_pointed`, `exists_tripling`, `exists_seven_times_ternary` and `cofinal_outside_product_closure`. A fresh Lean 4.33.1 build with warnings as errors compiled the binary seed, the harmonic construction and the tripling proof. Independent `leanchecker` replay passed for all three modules. All twelve printed declarations across those modules use only `propext`, `Classical.choice` and `Quot.sound`. [Replay instructions](../README.md#replay)

The 2026-11-28 searches covered DeepMind issues and PRs, the Left to Solve problem and solved ledger, and OMA issues and PRs. The OMA Alspach branch contains Bose and Skolem triple-system constructions. The searches found no matching quadruple-system tripling proof. [DeepMind statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5495) · [Left to Solve](https://lefttosolve.com/p/Erdos722.erdos_722) · [OMA Alspach PR](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/12713) · [OMA quadruple-system search](https://github.com/GuillaumeBAUD-coder/open-math-agents/pulls?q=is%3Apr+%22Steiner+quadruple%22)
