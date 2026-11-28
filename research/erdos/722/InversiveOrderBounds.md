# A superquadratic lower bound for orders of Steiner 3-designs

Let $p$ be a prime congruent to 3 modulo 4. Every ordinary Steiner system $S(3,2p+1,v)$ on $v>2p+1$ points satisfies

$p^6(2p+1)\le v^3.$

At block size $k=2p+1$, this says $v\ge (k-1)^2 k^{1/3}/4$. For every natural $C,B$, the checked theorem gives a prime $p>B$ such that every nontrivial design at this block size has $v>Ck^2$. The quantifier on designs is conditional on their existence. Keevash proved eventual existence classically. The notebook proves an order bound and uses the exact `Finset.IsBlockDesign` predicate from Erdős 722. For example, every nontrivial $S(3,215,v)$ has at least 68,588 points. [Lean statement](Erdos722InversiveBruckRyser.lean.in) · [Pinned Erdős 722](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/722.lean) · [Keevash, *The existence of designs*](https://arxiv.org/abs/1401.3665)

## Why the order grows

Write $q=2p$. Cameron's bound and the preceding minimum-order classification give $v\ge q^2+1$ for these block sizes. At equality, the derivative at a point would be an affine plane of order $q$, hence would give a projective plane of that order. Bruck–Ryser rules this out. Indeed $q\equiv 2\pmod4$, and the prime $p\equiv3\pmod4$ occurs to odd exponent in $q$. [Minimum orders](MinimumSteinerOrders.md) · [Bruck and Ryser, 1949](https://doi.org/10.4153/CJM-1949-009-2) · [Dugongue's checked Lean proof](https://github.com/lefttosolve2/open-math-agents/pull/1091)

For $v>q^2+1$, the pair replication test gives $v=q^2+1+(q-1)d$ with $d>0$. The point test gives $p\mid(v-1)(v-2)$, so $d+e=ph$ for some $e\in\{0,1\}$ and $h\ge1$. The total block count gives $2p+1\mid v(v-1)(v-2)$. Reducing $v$ modulo $2p+1$ now replaces it by $h+2e+2$. Consequently

$2p+1\mid(h+2e)(h+2e+1)(h+2e+2).$

This product is positive and at most $(h+4)^3$. Substituting $d=ph-e$ into the order gives $v\ge p^2(h+4)$ for $p\ge3$, yielding the claimed inequality. The cubic estimate holds on the binomial tests alone for every prime $p\ge3$ and every $v>(2p)^2+1$. The geometry excludes the boundary for the stated prime family. [Spacing at prime divisors](Erdos722SquareOrderSpacing.lean) · [Cubic bound for admissible orders](Erdos722CubicOrderBound.lean)

## Square order, signed designs and the cutoff

For each $q\ge2$, the existence of an $S(2,q,q^2)$ is equivalent to the existence of a finite mathlib `Configuration.ProjectivePlane` of order $q$. Every point lies on $q+1$ blocks. At a point outside a block, exactly $q$ of those lines meet the block, leaving a unique parallel. Completing the parallel classes adds $q+1$ points and one line. Conversely, deleting any line of a projective plane leaves $q^2$ points and truncates each remaining line at its unique intersection with the deleted line. The notebook implements the constructions on the canonical finite designs. Synthetic affine-to-projective completion was formalized independently by Schwahn. [Parallel classes](Erdos722AffineParallelClasses.lean) · [Completion](Erdos722AffineCompletion.lean) · [Line deletion and point derivatives](Erdos722ProjectiveDeletion.lean) · [Schwahn's incidence geometry](https://github.com/PSchwahn/IncidenceGeometry)

For $s\ge0$, deriving $s$ times shows $S(2+s,q+s,q^2+s)$ implies a plane of order $q$. When $q\equiv1,2\pmod4$, Bruck–Ryser therefore forces $q$ to be a sum of two squares. The converse above concerns $s=0$. In rank three, $q^2+1$ always passes all the binomial tests for block size $q+1$, with replication numbers $q(q^2+1),q(q+1),q+1$. For $q\equiv6,21,30,33\pmod{36}$, the sum of two squares condition fails already modulo 9. Each such order has a signed index-one realization and no ordinary realization. [Binomial tests and signed designs](Erdos722InversiveOrder.lean) · [Classical derived-plane obstruction](https://doi.org/10.1007/s10623-026-01888-w)

At $k=36t+7$, every cutoff $N$ that guarantees existence at all admissible $v\ge N$ satisfies $N>(k-1)^2+1$. This improves the preceding quadratic bound at these block sizes. The stronger order estimate above also uses gaps between admissible orders, so it bounds orders supporting a design. For $k=7$, the square obstruction excludes 37, and every order from 38 through 76 fails a binomial test. Thus $v\ge77$ for every nontrivial design. The replay checks admissibility at 77. Attainment remains a separate question. Balachandran identified 77 as the first possible order in the concluding remarks of his paper. [Earlier signed family](Erdos722SignedTripleFamily.lean) · [Balachandran, *New infinite families of Candelabra systems*](https://www.math.iitb.ac.in/~niranj/papers/newcandelabras.pdf)

## Source and replay

The supplemental replay verifies the digest of Dugongue's original Bruck–Ryser source at OMA commit `819608fccbdb8a58c5b7f503607e93c05619731d`, builds it unmodified and checks the axioms of `OMA.solution`. The pinned Erdős 723 declaration supplies its type. Wang and Uskuplu also formalized Bruck–Ryser–Chowla for symmetric designs. The contribution here combines the canonical design-to-plane construction with the replication constraints and the quantitative order estimate. [Pinned certificate](https://github.com/lefttosolve2/open-math-agents/blob/819608fccbdb8a58c5b7f503607e93c05619731d/proofs/Erdos723.erdos_723.variants.bruck_ryser.lean) · [Pinned Erdős 723](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/723.lean) · [Wang and Uskuplu](https://doi.org/10.4230/LIPIcs.ITP.2026.19)

From the pinned Formal Conjectures checkout, run `lake env python3 "$NOTEBOOK/research/erdos/722/replay-inversive-orders"`. Pass `--certificate FILE` to reuse the pinned source locally. The runner compares the exact 722 and Bruck–Ryser statements, checks orders 37 and 77 and the numerical bound at $p=107$, and replays each module in a separate kernel invocation. The ordinary notebook runner also accepts `Erdos722CubicOrderBound` for the arithmetic and geometric constructions. [Supplemental runner](replay-inversive-orders) · [Left to Solve 722](https://www.lefttosolve.com/p/Erdos722.erdos_722) · [OMA reduction](https://github.com/lefttosolve2/open-math-agents/pull/17505)

The independent run on Lean 4.33.1 replayed 25 notebook and adapter modules and the original certificate. All 26 public theorems added here and `OMA.solution` use only `propext`, `Classical.choice` and `Quot.sound`.
