# Typical automorphism groups of split four-fibre Steiner quadruple systems

Let $n=2^d$ and $m=\binom{n-1}{2}$. The normalized split construction produces $6^m$ distinct labelled Steiner quadruple systems on $4n$ points. As $d\to\infty$, the proportion with binary incidence rank $4n-d-1$ and full automorphism group of the minimum order $4n^2$ tends to one. For $d\ge8$ this proportion is at least $1-2^{-d}$. [Proportion and limit](Erdos722TypicalFourFibreAsymptotics.lean) · [group structure for typical words](Erdos722TypicalFourFibreSystems.lean) · [previous sharp minimum](FourFibreAutomorphisms.md)

Let $C_d$ count the classes represented by the split family, identifying systems under every permutation of the $4n$ points. Put $G_d=6|\mathrm{GL}(d,2)|$. Then
$$
\left|\frac{G_d C_d}{6^m}-1\right|\le 2^{-d}\qquad(d\ge8).
$$
In particular $C_d\sim 6^m/G_d$. The split filling fixes the transversal rule, and the normalization sets all pair matchings incident to the root to the identity. The count ranges over the resulting family. The host Erdős 722 declaration asks for eventual existence at **every** admissible order for **every** fixed pair of strengths and block sizes. Here the strength is three, the block size is four, and the orders are $4\cdot2^d$. [Class count](Erdos722SplitClassMass.lean) · [asymptotic](Erdos722TypicalFourFibreAsymptotics.lean) · [pinned host](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/722.lean)

## How often does a word have an extra symmetry?

A word assigns a permutation of three fibre directions to each nonroot edge. Reversing the orientation inverts the permutation. Call a word typical if the root is its unique all-identity star and only the identity rooted frame preserves it. A rooted frame consists of a linear permutation of the base cube and one common permutation of the three directions. For a typical word the full point automorphisms are precisely the translations by two affine binary checks. They form an elementary abelian group of order $4n^2$. [Normalized matchings](Erdos722FourFibreEdges.lean) · [rooted frames](Erdos722MatchingFrameCounts.lean) · [typical designs](Erdos722TypicalFourFibreSystems.lean)

If $B_d$ is the number of exceptional words, then
$$
B_d\le(n-1)6^{m-(n-2)}
      +6n^d\,6^{m-(n-3)}
      +5\cdot3^m.
$$
In this formula differences in the natural-number exponents truncate at zero. A second star forces all $n-2$ nonroot letters meeting its centre. For a nonidentity rooted base map $b$, choose $x$ with $bx\ne x$. Take the set of edges incident to $x$ and omit the single possible edge also incident to $b^{-1}x$. This leaves at least $n-3$ edges. The image under $b$ of each retained edge lies outside this set, so the frame equation determines its letter from a letter outside the set, inverting it if the orientation changes. The images of a basis give at most $n^d$ rooted base maps. Finally, any nonidentity pure colour has centralizer of size at most three in $S_3$. A word with a common fixed direction already admits such a pure colour symmetry. [Determined coordinates](Erdos722DeterminedMatchingEdges.lean) · [second stars](Erdos722MatchingStarEdges.lean) · [moved rows](Erdos722MovedMatchingRow.lean) · [union bound](Erdos722ExceptionalMatchingWords.lean)

## Counting actual point-isomorphism classes

For typical words the binary checks recover the four-point fibres. A point isomorphism carries identity stars to identity stars, hence it fixes the root on the base. Its base permutation is linear over the binary field, and its common fibre colour acts on letters by conjugation. Conversely, each rooted coordinate change gives a point isomorphism. The rooted action on typical words is free. Thus each typical class contains exactly $G_d$ typical words. All exceptional words together can add at most $B_d$ further classes. For $d\ge8$, the finite estimate $2^d(6n^d)B_d\le6^m$ controls the error even after multiplying by the size of a rooted orbit. [Rooted action](Erdos722RootedWordAction.lean) · [point isomorphisms](Erdos722TypicalPointOrbits.lean) · [scaled exceptional mass](Erdos722ScaledMatchingError.lean)

At $d=2$ an independent enumeration of all $6^3=216$ words found 36 typical words. Enumerating base permutations and simultaneous colour conjugations gave a single typical class of size 36.

## Sources and replay

D. V. Zinoviev and V. A. Zinoviev describe the underlying fixed-corank construction. Their order-16 rank classification and the labelled rank enumerations of Xu and Shi cover different counting questions. The results here concern the relative frequency of the minimum group and the number of unlabelled systems in the normalized split family. Historical priority for these formulas is unestablished. [Zinoviev and Zinoviev, construction II](https://www.moi.math.bas.bg/oc2013/p33.pdf#page=19) · [rank-13 classification](https://www.mathnet.ru/php/archive.phtml?jrnid=ppi&option_lang=eng&paperid=150&wshow=paper) · [Xu and Shi](https://doi.org/10.1016/j.disc.2020.111844)

The DeepMind definitions and packing results, the Left to Solve entry, and the Open Math Agents assembly and divisibility threads were checked for this statement. The personal notebook previously established the rank distribution and an explicit word attaining the minimum. [DeepMind definitions](https://github.com/google-deepmind/formal-conjectures/pull/5495) · [packings](https://github.com/google-deepmind/formal-conjectures/pull/4248) · [Left to Solve](https://www.lefttosolve.com/p/Erdos722.erdos_722) · [OMA assembly](https://github.com/lefttosolve2/open-math-agents/pull/35115) · [OMA divisibility](https://github.com/lefttosolve2/open-math-agents/pull/35931) · [rank distribution](https://github.com/vincentkoc/solved-conjectures/pull/388) · [explicit minimum](https://github.com/vincentkoc/solved-conjectures/pull/397)

From the pinned Formal Conjectures checkout, run `lake env python3 "$NOTEBOOK/scripts/replay-research" Erdos722TypicalFourFibreAsymptotics`.

Independent Lean 4.33.1 replay rebuilt and kernel-checked 87 notebook modules. The audit covered all 51 new public declarations and allowed only `propext`, `Classical.choice` and `Quot.sound`. Nineteen direct checks covered the host quantifiers and predicate, point relabelling, exceptional mass, orbit size and the two limits.
