# Asymmetric quadruple systems with independent coefficients on a coset

Let $d\ge6$, $n=2^{d+2}$ and $b(v)=\binom v3/4$. The family below contains exactly
$$
216^{b(n/4)}\,4^{b(n)-n}
$$
isomorphism classes of Steiner quadruple systems on $4n$ points. Every member has binary incidence rank $4n-d-3$ and trivial full point automorphism group. Isomorphisms may permute all $4n$ points. At $d=6$ this gives $216^{10416}4^{690624}$ classes on 1,024 points, each of rank 1,015. [Exact count and finite specialization](Erdos722CosetAsymmetricCount.lean) · [rank and full point group](Erdos722CosetDesignIsomorphisms.lean)

## Construction

Take the affine binary quadruple system on $V=\mathbb F_2^{d+2}$ as base and replace each point by a fibre $F=\mathbb F_2^2$. Use the rigid matching from the earlier four-fibre construction. Use one private base block at each of the $d+3$ affine-basis points. On that block, give the marked point a fixed three-cycle of the nonzero fibre vectors. This fixes a labelled matching and marked incidences throughout the family. [Marked systems](MarkedPointGroups.md)

The coset $U$ consisting of vectors with first two coordinates equal to one misses the entire affine basis. Prefixing two ones embeds the affine quadruple system on $2^d=n/4$ points, giving $b(n/4)$ variable base blocks. None is a private marked block. In each variable block choose one origin. At that point use the identity linear map on $F$. At each of the other three points choose any element of $\mathrm{GL}(2,2)$, independently. Each block has $6^3=216$ coefficient patterns. Finally choose an unrestricted offset $u_B\in F$ on every base block. The transversal relation on $B$ is
$$
\sum_{i\in B} C_{B,i}x_i=u_B .
$$
Because each coefficient is invertible, three points determine the fourth. The fixed rules on repeated fibres complete the design. [Coset blocks](Erdos722AffineCosetBlocks.lean) · [coefficient patterns](Erdos722CosetCoefficientPatterns.lean) · [four-fibre completion](Erdos722BlockwiseFibreCoordinates.lean)

## Why different patterns give different classes

Binary parity checks recover the fibres. The variable coset and all private blocks together occupy at most $2^d+4(d+3)$ base points, strictly less than $n/2$. Any proposed base permutation therefore sends at least one point with ordinary transversal equations to another such point. Comparing completions through this point recovers the global linear part of each fibre map. Rigidity of the base matching forces the base permutation and the common linear part to be identities. Every possible isomorphism has the form $(i,x)\mapsto(i,x+t_i)$. [Translations between fillings](Erdos722TranslationsBetweenFillings.lean)

Translations change only the constant term of each block equation. The normalized coefficients can be read from the relation by using the block origin as output, varying one other input and subtracting the output at zero. All three linear maps are recovered. Thus two distinct patterns cannot become isomorphic through a change of coordinates. [Coefficient recovery](Erdos722RecoverBlockCoefficients.lean)

For an automorphism, the equations through an ordinary point force the translation function $t$ to be affine on the base. Each private marked equation then forces its basis value to be a fixed vector of the chosen three-cycle, hence zero. An affine function vanishing on the whole affine basis is zero. Every design is therefore asymmetric. For each fixed pattern, the $4^n$ fibre translations produce distinct offsets in one isomorphism class. Dividing the $216^{b(n/4)}4^{b(n)}$ labelled parameter choices by $4^n$ gives the formula. [Translation kernel](Erdos722CosetTranslationKernel.lean) · [unrestricted class fibres](Erdos722CosetAsymmetricCount.lean)

## Scope and attribution

Zinoviev and Zinoviev's Construction II allows independent transversal codes in systems of fixed binary corank. Mendelsohn previously realized every finite group as the full automorphism group of some finite quadruple system, including the trivial group. The earlier notebook theorem counted offsets with one fixed marked coefficient pattern. The additional factor here counts independently recoverable patterns on all blocks of an affine coset at the same order and rank. The formula counts the constructed family. Historical priority for this particular count is unestablished. [Zinoviev and Zinoviev](https://www.moi.math.bas.bg/oc2013/a33.pdf) · [Mendelsohn](https://doi.org/10.1016/0097-3165%2878%2990072-9) · [previous marked family](https://github.com/vincentkoc/solved-conjectures/pull/428)

The host asks for an existence theorem for every $1\le r<k$ and every sufficiently large admissible order, a classical theorem of Keevash. This family uses its exact `Finset.IsBlockDesign 3 4` predicate at the displayed orders and additionally classifies the resulting designs. Live DeepMind, Left to Solve, OMA and notebook searches found no matching class count. [Pinned host](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/722.lean) · [DeepMind design definitions](https://github.com/google-deepmind/formal-conjectures/pull/5495) · [Left to Solve](https://www.lefttosolve.com/p/Erdos722.erdos_722) · [OMA assembly](https://github.com/lefttosolve2/open-math-agents/pull/35115)

## Verification

From the pinned Formal Conjectures checkout run `lake env python3 "$NOTEBOOK/scripts/replay-research" Erdos722CosetAsymmetricCount`.

An independent finite calculation distinguished all $216\cdot4=864$ local relations and checked uniqueness of each input for a prescribed output. On the 256-point base it counted 690,880 quadruples, including exactly 10,416 inside the reserved coset. For one explicit set of private blocks and three different coefficient assignments, binary elimination gave full rank 512 for the translation equations.

Independent Lean 4.33.1 replay rebuilt and kernel-checked 102 notebook modules. All seven new objects matched the development build byte for byte. The audit checked 44 new public declarations against `propext`, `Classical.choice` and `Quot.sound`. Seventeen direct comparisons checked the pinned host quantifiers, block predicate, unrestricted point group, rank, exact cardinalities and the smallest supported order.
