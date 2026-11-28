# Transversal offsets for rigid four-point fibres

Fix $d\ge2$, put $n=2^d$, and let $b=\binom n3/4$. There is an explicit family of $4^b$ labelled Steiner quadruple systems on $4n$ points with exactly
$$
4^{b+d+1-n}
$$
isomorphism classes under all permutations of the points. Every member has binary incidence rank $4n-d-1$ and full elementary abelian automorphism group of order $4n^2$. At 16 points the four labelled systems give one class. At 32 points this construction gives 1,048,576 distinct classes of rank 28 and group order 256. [Explicit family](Erdos722RigidTransversalSpectrum.lean) · [labelled systems and rank](Erdos722TwistedCubeFamilies.lean) · [class count](Erdos722TwistedClassCount.lean)

## Construction

Use the binary affine quadruple system on the $n$ base points. Replace each point by a copy of $F=\mathbb F_2^2$. Keep the four-point fibre blocks and the pair matchings of the marked-path construction. For each base block $B$ choose a value $u_B\in F$. A transversal over $B$ is a block precisely when its four fibre coordinates sum to $u_B$. Any three points in distinct fibres determine their fourth point by this sum. Replacing one member of a completed triple by its fourth point recovers the same base block and cancels the same offset twice. This gives the host predicate for arbitrary choices of the offsets. [Path matching](Erdos722RigidPathMatching.lean) · [block offsets](Erdos722TransversalOffsets.lean) · [completion rule](Erdos722TwistedFourFibreRule.lean)

## Which choices are isomorphic?

A translation $t_i\in F$ at each point of the base changes the offset at $B$ by $(\partial t)_B=\sum_{i\in B}t_i$. The converse needs information about *every* point isomorphism. When the normalized matching has no common fixed direction, binary checks recognize the four-point fibres. Inside each fibre a permutation is affine. Subtracting the constant terms from the completion identity gives the split-system equation, which forces a single linear permutation of the three directions. The resulting base permutation and common colour preserve the pair matchings. For the marked path their joint stabilizer is trivial, so two systems are isomorphic exactly when $v-u$ lies in the range of $\partial$. The same criterion holds for any fixed matching with the two stated hypotheses. [Linear parts](Erdos722TwistedFibreFrame.lean) · [point isomorphisms](Erdos722TwistedPointIsomorphisms.lean) · [rigid matching criterion](Erdos722RigidTwistTranslations.lean)

The kernel of $\partial$ consists of the two-coordinate affine functions on the base. It has size $4^{d+1}=4n^2$ and acts as the full point automorphism group for every offset. Thus $4^n/4^{d+1}$ offset words represent each class. Dividing $4^b$ by this common class size gives the formula. [Incidence kernel](Erdos722TransversalIncidence.lean) · [affine checks](Erdos722FourFibreCube.lean) · [quotient equivalence](Erdos722TwistedClassCount.lean)

## Scope and sources

Zinoviev and Zinoviev's fixed-corank construction permits independent transversal codes on the base blocks. Their order-16 classification gives 4,131 isomorphism classes of rank 13. The count here fixes the pair matching and uses the four translated additive codes at each base block. The previous notebook results treated binary doublings and, for four-point fibres, the choice of pair matchings with zero transversal sums. The contribution here is the checked classification, exact count and full group for the offset family. Historical priority for the formula is unestablished. [Construction II](https://www.moi.math.bas.bg/oc2013/p33.pdf#page=19) · [order-16 classification](https://www.mathnet.ru/eng/ppi150) · [binary doublings](https://github.com/vincentkoc/solved-conjectures/pull/351) · [split automorphisms](https://github.com/vincentkoc/solved-conjectures/pull/397) · [split class counts](https://github.com/vincentkoc/solved-conjectures/pull/409)

The pinned Erdős 722 statement quantifies over every $1\le r<k$ and all sufficiently large admissible orders. This family realizes $r=3,k=4$ at $4\cdot2^d$ and counts its unlabelled members. The live DeepMind, Left to Solve and Open Math Agents records were checked for the host and the construction. [Pinned problem](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/722.lean) · [design definitions](https://github.com/google-deepmind/formal-conjectures/pull/5495) · [Left to Solve](https://www.lefttosolve.com/p/Erdos722.erdos_722) · [OMA assembly](https://github.com/lefttosolve2/open-math-agents/pull/35115) · [OMA divisibility](https://github.com/lefttosolve2/open-math-agents/pull/35931)

## Verification

From the pinned checkout run `lake env python3 "$NOTEBOOK/scripts/replay-research" Erdos722RigidTransversalSpectrum`.

An independent enumeration at $n=4$ checked all four offset choices, their 140 blocks, their rank 13, and explicit translations between them. At $n=8$ all 65,536 translations give exactly 256 distinct block sums, each with 256 lifts. Three independently generated 32-point systems each contained 1,240 blocks, covered all 4,960 triples exactly once, and had binary rank 28.

Independent Lean 4.33.1 replay rebuilt and kernel-checked 85 notebook modules. All 39 new public declarations used only `propext`, `Classical.choice` and `Quot.sound`. Seventeen direct comparisons covered the pinned predicate and quantifiers, the unrestricted quotient, the rank and the full point group.
