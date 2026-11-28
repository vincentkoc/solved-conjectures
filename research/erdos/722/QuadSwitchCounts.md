# Switching and counting Steiner quadruple systems

Let $H$ be a labelled Steiner quadruple system on $v$ points. Write $b=\binom v3/4$. On the doubled point set, fix the projection $(x,i)\mapsto x$. Call a system compatible with $H$ if each block is either two entire point fibres or projects onto a block of $H$. Exactly $2^b$ ordinary systems are compatible. They form a cube in which switching $d$ coordinates exchanges exactly $8d$ blocks in each direction. The four-point projections recover $H$ itself, so lifts of different labelled bases are disjoint. [Classification](Erdos722QuadSwitchClassification.lean) · [Block distance](Erdos722QuadSwitchCube.lean) · [Recovery and exact count](Erdos722CountCompatibleDoublings.lean)

## Construction and converse

For every base pair $x,y$, take all four points over it as a block. For each base block $B$, independently prescribe a parity. Include the eight sections of its four fibres whose second coordinates have that parity. A triple projecting to two points forces the first type of block. A triple projecting to three points selects a unique base block, and its three bits determine the fourth. Hanani gave the classical doubling construction. Colbourn explicitly describes the freedom to choose a parity for each block. [Hanani, *On quadruple systems*](https://doi.org/10.4153/CJM-1960-013-3) · [Colbourn, *Double Double Toil and Trouble*](https://cdc2020-math.uniri.hr/wp-content/uploads/2021/07/talk-colbourn.pdf) · [Two local families](Erdos722QuadSwitchSheets.lean) · [Transport to labelled blocks](Erdos722QuadSwitchTiles.lean) · [Ordinary construction](Erdos722QuadSwitchDoubling.lean)

The converse uses the minimum size of a trade. Take any finite, possibly nonuniform family of sets with integer weights. Suppose the weight through each set of at most $r$ points is zero. If a block has nonzero weight, at least $2^r$ distinct blocks have positive weight and at least $2^r$ have negative weight. A positive and a negative block differ at a point. Splitting at that point gives two nonzero weightings with vanishing rows through strength $r-1$. For $k$-uniform blocks, $r\le k$, the vanishing of just the $r$-rows implies all lower rows by double counting. Thus two distinct ordinary $S(r,k,v)$ differ by at least $2^r$ blocks per side. Hwang proved the classical minimum-volume theorem for trades. [Hwang, *On the structure of $(v,k,t)$ trades*](https://doi.org/10.1016/0378-3758(86)90131-X) · [Signed support proof](Erdos722MinimumTradeSupport.lean) · [Uniform packing and design distance](Erdos722MinimumDesignDistance.lean)

Over a fixed base block, the compatible family and the even parity family have exactly the same triple counts. If they differ, the trade bound forces all eight even sections out and all eight odd sections in. The two-fibre blocks are forced by their triples. This gives a unique parity vector, and a single changed bit attains the universal distance bound at rank three. The statement concerns distinct labelled systems. Some switched systems can be isomorphic. [Local rigidity](Erdos722QuadSwitchRigidity.lean) · [Sharp distance](Erdos722QuadSwitchOrders.lean)

## Iteration and unrestricted isomorphism

Write $L(v)$ for the number of labelled systems on $\mathrm{Fin}(v)$. Counting all compatible bases and both choices independently over every block gives $L(2v)\ge L(v)2^{b(v)}$, where $b(v)=\binom v3/4$ for an existing base system. For $N=2^m v$ and $E=\sum_{j<m}b(2^jv)$, there is a collection of $R$ pairwise nonisomorphic systems on $N$ points satisfying
$$
 R\,N!\ \ge\ L(v)\,2^{E},\qquad
 R\ \ge\ 2^{\max(0,E-\lceil\log_2(N!)\rceil)}.
$$
An isomorphism may use any permutation of the final point set. These bounds hold for every $m\ge0$ whenever a seed exists, including the vacuous host orders $v\le2$ and all $v\equiv2,4\pmod6$. The exact exponent satisfies
$$
168E=N^3-v^3-7(N^2-v^2)+14(N-v).
$$
For example, the successive orders $4,8,16,32$ contribute $1+14+140+1240=1395$ bits before reaching order 64. Since $\lceil\log_2(64!)\rceil=296$, the construction certifies at least $2^{1099}$ pairwise nonisomorphic ordinary systems there. The factorial bound allows every possible labelling, so the unlabelled counts are lower bounds. [Unrestricted representatives](Erdos722UnlabelledBlockFamilies.lean) · [Iterated counts](Erdos722IteratedSwitchCounts.lean) · [Orders, cubic identity and numerical instance](Erdos722QuadSwitchOrders.lean)

## Scope and replay

The notebook already has Hanani’s exact existence spectrum at $r=3,k=4$. The results here count and classify lifts of the specified projection. They use the pinned ordinary predicate throughout. Keevash established existence in all fixed ranks and stronger asymptotic estimates for the total number of designs. Lindner and Straley also used replacements in direct products to study isomorphism. The claims above concern this explicit construction and its Lean formalization. [Earlier notebook spectrum](QuadrupleSpectrum.md) · [Keevash, *Counting designs*](https://arxiv.org/abs/1504.02909) · [Lindner and Straley](https://dml.cz/handle/10338.dmlcz/105534) · [Pinned Erdős 722](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/722.lean)

The live DeepMind entries concern the statement and a separate packing problem. Left to Solve marks the general mathematical problem solved. Open Math Agents has a conditional general reduction and a rank-one equipartition proof. Neither supplies this rank-three classification or count. [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5495) · [Packing PR](https://github.com/google-deepmind/formal-conjectures/pull/4248) · [Left to Solve](https://www.lefttosolve.com/p/Erdos722.erdos_722) · [OMA reduction](https://github.com/lefttosolve2/open-math-agents/pull/17505) · [OMA rank one](https://github.com/lefttosolve2/open-math-agents/pull/17952)

From the pinned Formal Conjectures checkout, run `lake env python3 "$NOTEBOOK/scripts/replay-research" Erdos722QuadSwitchOrders`. [Notebook replay instructions](../../README.md#replay)

The clean replay covered 43 modules. An additional axiom audit checked all 75 public declarations in the twelve new proof modules. Three are axiom-free and the others use only standard Lean axioms. Thirteen comparisons against the pinned host and edge cases checked the design, compatibility and isomorphism predicates, binomial hypotheses, empty orders and the order-64 exponent.
