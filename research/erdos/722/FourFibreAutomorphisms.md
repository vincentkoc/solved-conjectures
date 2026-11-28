# Automorphisms of split four-fibre Steiner quadruple systems

For every $d\ge2$, put $n=2^d$. There is a labelled Steiner quadruple system on $4n$ points of binary rank $4n-d-1$ whose full automorphism group is elementary abelian of order $4n^2$. This is the least automorphism-group order among **all split systems** in the notebook's four-point matching construction on these labels. In fact $4n^2$ divides the group order for every matching word. The minimizing word is explicit. [Host design, rank, group and minimum](Erdos722SharpFourFibreAutomorphisms.lean) · [previous construction and rank distribution](FourFibreMatchingRanks.md)

### Which point permutations preserve the blocks?

Write a point as $(i,x)$, with $i$ in the base and $x\in\mathbb F_2^2$. The array $M_{ij}$ permutes the three nonzero fibre vectors and specifies the pair blocks. For three distinct base points, the fourth fibre coordinate is the sum of the first three. Suppose the base has at least three points, its binary checks separate them, some star consists of identity matchings, and the matchings have no common fixed direction. A **check** is a binary function whose sum on every block is zero.

Between two such systems the block isomorphisms are exactly the maps
$$
(i,x)\longmapsto \bigl(b(i),Lx+t(i)\bigr).
$$
Here $b$ preserves the ternary base completion, $L$ permutes the three nonzero vectors, and $L M_{ij}=M'_{b(i)b(j)}L$ for every pair. The two coordinates of $t$ are arbitrary base checks. Each point permutation determines the three parameters uniquely. An isomorphism can move the chosen star. [Isomorphism criterion and uniqueness](Erdos722SplitFourFibreIsomorphisms.lean)

The previous check-restriction theorem shows that points in one fibre agree on every check. Lifted base checks distinguish different fibres. This recovers the partition from the block set, even for arbitrary compatible transversal fillings. For the split filling, varying the same fibre coordinate at either of two base points gives the same fourth point in a transversal. Consequently the linear parts of the two fibre maps agree. The pair blocks then give the matching equation above. [Intrinsic partition](Erdos722IntrinsicFourFibres.lean) · [common linear part](Erdos722CommonFibreColour.lean) · [matching and translation equations](Erdos722FourFibreFrame.lean)

Let $C$ be the binary check space of the base, and $S$ the subgroup of base automorphism and colour pairs $(b,L)$ satisfying the matching equation. Then
$$
\operatorname{Aut}(D)\cong (C\times C)\rtimes S,\qquad ((b,L)\cdot t)(i)=L\,t(b^{-1}i).
$$
The proof supplies a multiplicative equivalence with the subgroup of all point permutations preserving the actual blocks. For the affine cube, checks are affine binary functions, so the translation subgroup has order $(2^{d+1})^2=4n^2$. It still acts for split words with a common fixed direction. [Semidirect product](Erdos722SplitFourAutomorphismGroup.lean) · [action on checks](Erdos722FourFibreShiftAction.lean)

### A word attaining the minimum

Number the root $0$ and the other vertices $1,\ldots,n-1$. Give every root edge and the edge $\{1,2\}$ the identity matching. Give every other consecutive edge the same transposition. Give all forward nonconsecutive nonroot edges the same three-cycle and the reverse edges its inverse.

The matching orders recover the path. Vertex $0$ is the unique all-identity star. Vertex $1$ is the only other vertex with no transposition edge. Its identity neighbour among the remaining vertices is $2$. From $2$ onwards the transposition edges determine each successor. Thus $b$ fixes every vertex, even among arbitrary base permutations. The colour must commute with the transposition on $\{2,3\}$ and the three-cycle on $\{1,3\}$, which forces $L=1$. The three-cycle also excludes every common fixed direction. The resulting word therefore has the stated rank and exactly the unavoidable translations. [Path rigidity](Erdos722RigidMatchingPath.lean) · [matching certificate](Erdos722RigidPathMatching.lean) · [labelled cube word](Erdos722RigidCubeWord.lean)

At $d=2$ the construction gives 16 points, rank 13 and 64 automorphisms. At $d=3$ it gives 32 points, rank 28 and 256 automorphisms. The construction uses $d\ge2$ so the nonroot path has at least three vertices. As an independent check, exhaustive extension of point maps under ternary completion gave the following orders for all 194 labelled split words of rank 13 on 16 points. The counts add to 194.

| Automorphism-group order | 64 | 128 | 384 | 768 | 1152 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Labelled words | 36 | 126 | 24 | 6 | 2 |

### Scope and sources

The pinned host asks for designs of every strength $1\le r<k$ at all sufficiently large admissible orders. Here the literal host predicate is `Finset.IsBlockDesign 3 4` on `Fin (4*2^d)`. The contribution determines automorphisms of the stated split family and gives a sharp minimum within it. The general existence theorem is due to Keevash. [Pinned Erdős 722](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/722.lean) · [Keevash](https://arxiv.org/abs/1401.3665) · [notebook Hanani spectrum](https://github.com/vincentkoc/solved-conjectures/pull/117)

D. V. Zinoviev and V. A. Zinoviev describe the underlying four-fibre construction and fixed-code counts. Their order-16 classification already includes all 4,131 isomorphism classes of rank 13. Kaski, Östergård and Pottonen tabulate automorphism-group orders for systems of order 16. Xu and Shi enumerate systems by binary rank. The per-array group isomorphism and the uniform marked-path witness are the scope of this formalization. Historical priority for the formulas is unestablished. [Fixed-corank construction](https://www.moi.math.bas.bg/oc2013/p33.pdf#page=27) · [rank-13 classification](https://www.mathnet.ru/php/archive.phtml?jrnid=ppi&option_lang=eng&paperid=150&wshow=paper) · [order-16 classification](https://pottonen.kapsi.fi/sqs16.pdf) · [Xu and Shi](https://doi.org/10.1016/j.disc.2020.111844)

The live DeepMind definition and packing PRs concern other statements. Left to Solve lists the host as research solved. The Open Math Agents threads concern assembly, divisibility and rank-one constructions. The live searches found no matching formalization of the isomorphism criterion or minimum. [Definitions](https://github.com/google-deepmind/formal-conjectures/pull/5495) · [packings](https://github.com/google-deepmind/formal-conjectures/pull/4248) · [Left to Solve](https://www.lefttosolve.com/p/Erdos722.erdos_722) · [OMA assembly](https://github.com/lefttosolve2/open-math-agents/pull/35115) · [OMA divisibility](https://github.com/lefttosolve2/open-math-agents/pull/35931)

From the pinned Formal Conjectures checkout, run `lake env python3 "$NOTEBOOK/scripts/replay-research" Erdos722SharpFourFibreAutomorphisms`.

Independent Lean 4.33.1 replay checked 50 freshly compiled notebook modules. All 55 new public declarations passed the axiom audit. Nineteen direct checks covered the pinned host quantifiers, the rank matrix, the block automorphism subgroup, orders 16, 32 and 64, and the divisibility bound in dimensions zero and one.
