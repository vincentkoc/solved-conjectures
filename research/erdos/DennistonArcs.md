# Denniston maximal arcs as Steiner pair designs

For every $q=2^e$ with $e>0$ and every $k=2^b$ with $b\le e$, `exists_denniston_design` constructs a Steiner pair design on $q(k-1)+k$ labelled points. At block size four the orders are $16,28,52,100,196,\ldots$. This is a Lean formalization of R. H. F. Denniston's 1969 construction. [Denniston, *Some maximal arcs in finite projective planes*, pp. 317–319](https://doi.org/10.1016/S0021-9800%2869%2980095-5) · [Lean proof](Erdos722DennistonArcs.lean)

## The points and blocks

In $K=\mathbb F_q$, choose $a$ outside the image of $t\mapsto t^2+t$. This additive map has a kernel of order two, so its image has index two. The quadratic form $Q(x,y)=x^2+xy+ay^2$ vanishes only at the origin. Let $H$ be an additive subgroup of order $k$. Take the points with $Q(x,y)\in H$ and intersect them with each affine line. The nonempty intersections are the blocks.

Along a line the form is $At^2+Bt+C$ with $A\ne0$. For $B=0$ the map is a bijection. For $B\ne0$ the line misses the origin, so the form never vanishes there. The additive part $f(t)=At^2+Bt$ has kernel $\{0,B/A\}$ and image of index two. If the line meets the arc, $H$ contains a point of the coset $C+\operatorname{im} f$ outside $\operatorname{im} f$. It follows that $H+\operatorname{im} f=K$ and $[K:f^{-1}H]=[K:H]$. Translating the parameters by one intersection point gives exactly $|H|$ points on the secant.

Two distinct arc points determine a unique affine line. The $q+1$ lines through the origin each have $k-1$ other arc points, yielding $1+(q+1)(k-1)=q(k-1)+k$ points in total.

## Scope and verification

The proof imports the pinned `Finset.IsBlockDesign` and produces `D.IsBlockDesign 2 (2 ^ b)` on the indicated `Fin` type. The upstream hypotheses $1\le r<k$ hold here for $r=2$ and $b\ge2$. For $0<b<e$, the order lies strictly between $2^{e+b-1}$ and $2^{e+b}$. Thus `frequently_denniston_design` gives cofinally many orders outside all powers of two at each fixed block size $4,8,16,\ldots$. The endpoint $b=e$ recovers the affine plane. Keevash's upstream theorem covers all sufficiently large admissible orders at every fixed $1\le r<k$. [Pinned Erdős 722](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/722.lean) · [Block-design predicate](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjecturesForMathlib/Combinatorics/Hypergraph/Finite.lean) · [Keevash, *The existence of designs*](https://arxiv.org/abs/1401.3665)

All eight printed declarations in `Erdos722.Denniston` use only `propext`, `Classical.choice` and `Quot.sound`. A clean Lean 4.33.1 build with warnings as errors and an independent `leanchecker` replay passed. [Replay instructions](../README.md#replay)

The 2026-11-28 overlap searches covered DeepMind issues and PRs, the Left to Solve target and solved ledger, OMA issues and PRs, the personal notebook and indexed Lean code. Left to Solve listed the full target as unsolved with zero active agents. The two OMA Denniston hits cite a different paper about planes of order ten. The notebook's earlier quadruple systems and projective sublines cover triples. [DeepMind statement](https://github.com/google-deepmind/formal-conjectures/pull/5495) · [Left to Solve](https://lefttosolve.com/p/Erdos722.erdos_722) · [OMA order-ten reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/331) · [Related OMA reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/377) · [Projective sublines](ProjectiveSublines.md)
