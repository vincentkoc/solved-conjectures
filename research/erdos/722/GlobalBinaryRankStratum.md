# Full automorphism groups one binary rank above the minimum

Let $n=2^d$ with $d\ge7$. Consider every Steiner quadruple system on $2n$ points whose binary block-by-point incidence matrix has rank $2n-d-1$. This is one above the minimum. Write $N$ for its number of isomorphism classes under all point permutations and $L$ for its number of systems on a fixed set of $2n$ labels. Put
$$
 b=\binom n3/4,\qquad E=\lfloor n^3/1024\rfloor,\qquad
 G=2^n n\prod_{i=0}^{d-1}(n-2^i).
$$

The full automorphism group is isomorphic to $(\mathbb Z/2)^{d+1}$ except for at most a fraction $1/(n2^E)$ of classes and at most a fraction $1/(2n2^E-1)$ of labelled systems. Both sample spaces are nonempty. At 256 points the minimum rank is 247. At rank 248 the two exceptional fractions are at most $2^{-2055}$ and $1/(2^{2056}-1)$, respectively. [Enumeration and existence](Erdos722ClosedRankEnumeration.lean) · [Unrestricted classes](Erdos722GlobalRankSymmetry.lean) · [Uniform labelled systems](Erdos722LabelledRankSymmetry.lean)

The same proof gives the exact labelled mass and a finite interval for the number of classes.
$$
 LG=(2^b-2^{n-d-1})(2n)!,\qquad
 0\le (N+1)G-2n\,2^b\le 2^{b-E}.
$$
The extra class in $N+1$ is the affine design, which has minimum rank. The labelled identity also holds for all $d\ge0$. It gives zero systems at $d=2$ and 995350356000 at $d=3$. Tonchev derived the labelled enumeration, proved exponential growth of the number of isomorphism classes and classified order 16 at rank 12. [Labelled mass](Erdos722LabelledRankMass.lean) · [Tonchev (2003)](https://digitalcommons.mtu.edu/math-fp/125/)

## Recognizing the whole stratum

A binary check assigns a bit to each point with zero sum on every block. These checks form the kernel of the incidence matrix. Evaluating all checks at a point and translating by the evaluation at a fixed origin defines its signature. The signatures fill a binary vector space, and its affine functions give exactly the checks. For two fixed distinct points, completion of a triple defines an involution on the points, extended by interchanging the fixed pair. Its effect on signatures is translation by the sum of the pair's signatures. As a result every signature fibre has the same size. This argument applies to arbitrary finite Steiner quadruple systems with a chosen point. [Incidence and kernel](Erdos722BinaryIncidenceRank.lean) · [Affine dual](Erdos722AffineSignatureDual.lean) · [Equal fibres](Erdos722EqualSignatureFibres.lean)

At rank $2n-d-1$ the number of distinct signatures is $n$, so the fibres are pairs. Blocks consist of two complete pairs or project bijectively onto an affine plane. This recovers a presentation by switches on the $b$ blocks of the affine design on $n$ points. Conversely a switch gives the required rank exactly when it is not a coboundary, meaning it cannot be written as the block sums of a function on base points. This discharges the projection hypothesis in the earlier switch count. The carrier agrees with the classical description using repeated columns of a first-order Reed–Muller code. [Projection](Erdos722BinaryProjectionBlocks.lean) · [Whole-stratum equivalence](Erdos722WholeRankStratum.lean) · [Assmus (1995)](https://doi.org/10.37236/1203) · [Earlier switch bound](BinaryDoubleSymmetry.md)

## Counting classes and labellings

The affine base admits exactly $n\prod_{i<d}(n-2^i)$ point automorphisms, from the choice of origin image and ordered basis. Independent flips of the $n$ fibres give the factor $2^n$ in $G$. There are exactly $2^{n-d-1}$ coboundary switches, all in the affine class. For each remaining switch its stabilizer in the group of order $G$ is its full automorphism group. This stabilizer contains the elementary abelian check subgroup of order $2n$. Every exceptional stabilizer has order at least $4n$. [Base permutations](Erdos722AffineBasePermutations.lean) · [Affine class weight](Erdos722AffineClassWeight.lean) · [Class stabilizers](Erdos722RankClassStabilizers.lean)

If $B$ counts the exceptional classes, orbit–stabilizer gives $BG\le 2((N+1)G-2n\,2^b)$. Applying the earlier Burnside bound controls $B/N$. A class with stabilizer $A$ contributes $(2n)!/|A|$ labellings. Thus an exceptional class contributes at most half the weight of an ordinary class, giving the second exceptional fraction. [Orbit defect](Erdos722RankOrbitDefect.lean) · [Labelling orbits](Erdos722LabelledRankOrbits.lean)

## Host statement and prior work

The design predicate is the pinned host's `Finset.IsBlockDesign 3 4`. The statements concern a specified binary rank at orders $2^{d+1}$. Keevash proved eventual existence for all fixed admissible parameters. Prior finite-rank work also includes the Zinovievs' classification at order 16. The contribution here is a checked whole-stratum equivalence, an explicit class-count error, and full-group estimates for both sampling conventions. Historical priority for the quantitative bounds is unestablished. [Pinned Erdős 722](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/722.lean) · [Keevash](https://arxiv.org/abs/1401.3665) · [Zinoviev and Zinoviev](https://www.mathnet.ru/php/archive.phtml?jrnid=ppi&option_lang=eng&paperid=150&wshow=paper)

DeepMind's entries cover the host statement and asymptotic packings. Left to Solve lists the general problem as research solved. Open Math Agents has the absorption reduction, its deterministic assembly step and the rank-one subproblem. The live checks found no corresponding formal whole-stratum automorphism bounds. [DeepMind statement](https://github.com/google-deepmind/formal-conjectures/pull/5495) · [Packings](https://github.com/google-deepmind/formal-conjectures/pull/4248) · [Left to Solve](https://www.lefttosolve.com/p/Erdos722.erdos_722) · [OMA reduction](https://github.com/lefttosolve2/open-math-agents/pull/17505) · [OMA assembly](https://github.com/lefttosolve2/open-math-agents/pull/35115) · [OMA rank one](https://github.com/lefttosolve2/open-math-agents/pull/17952)

From the pinned Formal Conjectures checkout, run `lake env python3 "$NOTEBOOK/scripts/replay-research" Erdos722ClosedRankEnumeration`. [Replay instructions](../../README.md#replay)

Independent kernel replay covered all 60 modules in the import closure on Lean 4.33.1. All 84 public declarations in the 18 added modules used only `propext`, `Classical.choice` and `Quot.sound`. Eighteen comparisons checked the pinned host type, ranks, both exceptional fractions and small examples.
