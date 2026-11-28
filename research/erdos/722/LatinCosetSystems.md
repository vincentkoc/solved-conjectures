# Asymmetric Steiner quadruple systems with arbitrary Latin cube fillings

Let $d\ge6$, $n=2^{d+2}$ and $b(v)=\binom v3/4$. The construction gives exactly
$$
13824^{b(n/4)}\,4^{b(n)-n}
$$
isomorphism classes of Steiner quadruple systems on $4n$ points. Every member has binary incidence rank $4n-d-3$ and trivial full point automorphism group. Isomorphisms may permute all $4n$ points. [Exact count and rank](Erdos722LatinCosetClassCount.lean) · [full point group](Erdos722LatinTranslationClasses.lean)

The earlier affine-coefficient construction embeds with its original labels. Write $A$ for its set of unrestricted classes at this order. Removing $A$ leaves exactly $(64^{b(n/4)}-1)|A|$ classes in the new family. At 1,024 points the rank is 1,015, $b(n/4)=10416$ and $|A|=216^{10416}4^{690624}$. [Label-preserving embedding and class difference](Erdos722LatinClassDifference.lean) · [earlier count](CosetAsymmetricSystems.md)

## Filling one block

Use the affine binary quadruple system on $V=\mathbb F_2^{d+2}$ and replace each point by a fibre $F=\mathbb F_2^2$. Keep the rigid pair matching and private marked coefficients from the earlier family. Reserve the affine coset $U$ of vectors starting in two ones. It contains $n/4$ points and $b(n/4)$ base blocks. Choose the constant term of the existing transversal equation freely on every base block outside the reserved collection. [Base, marked support and coset](CosetAsymmetricSystems.md)

Number the four fibres above each reserved block and identify the fibre symbols with $0,1,2,3$. Independently choose any ternary quasigroup $q$ on these symbols. Its graph consists of the 64 transversal blocks satisfying $q(x_0,x_1,x_2)=x_3$. Knowing three coordinates determines the fourth, including when an input is missing. A general replacement lemma combines these graphs with the original completion on every other triple. The resulting system satisfies the host's exact block-design predicate. The parity checks that compute its rank use the base projection and the pair matching. [Four-coordinate completion](Erdos722LatinFibreLaws.lean) · [replacement lemma](Erdos722TransversalReplacement.lean) · [design and rank](Erdos722LatinCosetSystems.lean)

### The local count

Normalize the three axes by requiring $q(x,0,0)=q(0,x,0)=q(0,0,x)=x$. A labelled cube is uniquely recovered from its normalized cube, one output symbol and three permutations fixing zero. This contributes $4(3!)^3=864$ choices. To enumerate normalized cubes, encode each row by four base-four digits. Each extension must be a permutation row and disagree in every position with the earlier rows on either intersecting slice. The proof shows that every normalized cube survives. Kernel evaluation checks that the final 64 row lists are distinct, decode to normalized Latin cubes, and re-encode to themselves. Thus the number of labelled cubes is $64\cdot864=55296$. This recovers the classical enumeration of order-four ternary quasigroups. [Axis bijection](Erdos722LatinCubeNormalization.lean) · [exhaustiveness](Erdos722ReducedLatinRows.lean) · [kernel count](Erdos722LatinCubeCount.lean) · [Krotov and Potapov](https://arxiv.org/abs/0912.5453)

## Global identifications

Parity checks recover the fibres under any point isomorphism. The coset and all private marks together miss more than half the base, so any base permutation carries some ordinary point to an ordinary point. The transversal equations through that pair force a common linear part in all fibre maps. The rigid matching then forces the base permutation and the linear part to be identities. Only translations $(i,x)\mapsto(i,x+t_i)$ survive. [Isomorphism reduction](Erdos722LatinCosetSystems.lean)

The exterior offsets distinguish every translation. A translation stabilizing them satisfies the ordinary four-term equation through a clean point and hence is affine on the base. The private marked equations force its value at each affine-basis point to vanish. Thus it vanishes everywhere. On a reserved block the translation acts by four coordinate relabellings of its Latin graph. The labelled block set recovers every graph and exterior offset, so the orbit of each parameter has exactly $4^n$ elements. Dividing $55296^{b(n/4)}4^{b(n)-b(n/4)}$ by $4^n$ gives the count above. [Exterior kernel](Erdos722ExteriorTranslationKernel.lean) · [parameter recovery](Erdos722LatinParameterRecovery.lean) · [translation orbits](Erdos722LatinTranslationClasses.lean)

For the embedding, solve the earlier four-term affine equation for the symbol in position three. Its graph is precisely that equation, independently of the numbering of the base block. The two labelled completions agree on every triple. Consequently the factor $64^{b(n/4)}$ compares nested sets of unrestricted point-isomorphism classes. [Affine cubes](Erdos722AffineLatinFillings.lean) · [exact difference](Erdos722LatinClassDifference.lean)

## Scope and verification

Zinoviev and Zinoviev's Construction II allows independent transversal codes for systems of fixed binary corank. Mendelsohn realized every finite group as the full automorphism group of some quadruple system. The result here counts this specified asymmetric family with all local Latin choices on the reserved coset, and identifies its exact difference from the earlier notebook family. Historical priority for these particular counts is unestablished. [Zinoviev and Zinoviev](https://www.moi.math.bas.bg/oc2013/a33.pdf) · [Mendelsohn](https://doi.org/10.1016/0097-3165%2878%2990072-9) · [earlier notebook family](https://github.com/vincentkoc/solved-conjectures/pull/437)

The pinned Erdős 722 statement asks for every $1\le r<k$ and every sufficiently large admissible order. This result uses its exact `Finset.IsBlockDesign 3 4` at $4\cdot2^{d+2}$ points. Searches of DeepMind, Left to Solve, Open Math Agents and the notebook found related design definitions and work on existence. They found no matching unrestricted class difference. [Pinned statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/722.lean) · [DeepMind definitions](https://github.com/google-deepmind/formal-conjectures/pull/5495) · [Left to Solve](https://www.lefttosolve.com/p/Erdos722.erdos_722) · [OMA assembly](https://github.com/lefttosolve2/open-math-agents/pull/35115)

From the pinned Formal Conjectures checkout, run `lake env python3 "$NOTEBOOK/scripts/replay-research" Erdos722LatinClassDifference`.

An independent enumeration by Latin square slices found 22, 14, 14 and 14 normalized cubes for the four possible first slices. Explicit expansion gave 55,296 distinct labelled tables, including all 864 tables defined by normalized affine equations and exactly 54,432 outside that subset.

Independent Lean 4.33.1 replay rebuilt and kernel-checked all 114 notebook modules in the dependency closure. The 12 new proof objects matched the development build byte for byte. All 107 new public declarations passed the axiom audit against `propext`, `Classical.choice` and `Quot.sound`, including eight that use no axioms. Seventeen comparisons checked the canonical host quantifiers and block predicate, unrestricted point isomorphisms, the labelled embedding, the class difference and the 1,024-point specialization.
