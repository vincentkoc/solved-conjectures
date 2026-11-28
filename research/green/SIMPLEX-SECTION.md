# Twenty-four labels force an affine three-space

Every set \(A\) of 24 points in \(\mathbb F_2^{12}\) has a translate of a three-dimensional subspace inside \(A+A\). The same conclusion holds for 23 points if 18 lie on a common affine hyperplane. Together with the explicit 20-point counterexample, this places the least forcing cardinality in \([21,24]\). [Twenty-four labels and the hyperplane criterion](Green51TwentyFourLabels.lean) · [Twenty-point counterexample](Green51TwelveAffineWitness.lean)

For Green's original quantity \(F(12,\alpha)\), the guaranteed dimension is exactly three on \(23/4096<\alpha\le25/4096\), and at least three for every \(23/4096<\alpha\le1\). One admissible 25-point set throughout the exact interval has no linear three-space in its double. The general density question remains open. [Density theorems](Green51TwentyFourBounds.lean) · [Pinned Green 51](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

## The fifteen-point section

Suppose a set of 18 labels in a binary eleven-space has no affine three-space in its double. Its augmented column code has no weight-sixteen word. The weight enumerator then forces a weight-three word in the dual. This word evaluates an affine functional that vanishes on precisely 15 labels. The three remaining labels belong to the other level. [Weight enumerators](Green51ShortenedProfiles.lean) · [Extracting the section](Green51EighteenSection.lean)

Within that ten-dimensional level, any 15 labels with no four- or six-label zero sum are affinely equivalent. In binary coordinates a representative is

\[
  0,1,2,4,8,16,32,64,128,256,512,685,822,967,1016.
\]

The relation code is the binary simplex code of length 15 and dimension four. Each nonzero word has weight eight, and the fifteen nonzero column functionals occur once each. Bonisoli classified equidistant linear codes in general. Here the binary argument supplies a coordinate permutation, then equality of the relation spaces gives an affine equivalence between the label sets. [Bonisoli, *Ars Combinatoria* 18 (1984), 181–186](https://unimore.unifind.cineca.it/resource/item/19917?language=en-US) · [Affine uniqueness](Green51FifteenSection.lean) · [Representative](Green51SimplexModel.lean)

## The exterior triple and pair

A pair of additional labels in one parallel ten-flat contributes its difference to the original ten-space. Two explicit symmetries reduce the nonzero differences outside a list of 28 possibilities to five representative obstructions. A difference there either repeats a pair of simplex labels or already completes an affine three-space. Two distinct listed differences present in the double must also have their sum on the list. [Finite direction orbits](Green51SimplexDirections.lean) · [Single and paired obstructions](Green51SimplexExtension.lean)

All 28 listed directions have value one under the quadratic form \(x_2x_6+x_1x_7+x_0x_8\). The sum of the values of a quadratic form on a binary three-space is zero. The three differences of the exterior triple form a plane, so any further compatible direction must be one of those three. If a disjoint exterior pair supplies that same difference, its four labels give a zero sum, which also forces a linear three-space. [Quadratic calculation](Green51QuadraticDirections.lean) · [Triple and pair theorem](Green51SimplexFibres.lean)

In dimension twelve there are four cosets of the direction space of the fifteen labels. Among 23 labels, five remain after removing the fifteen and the exterior triple. Two of the five belong to the same coset. This proves the hyperplane criterion. A hypothetical flat-free 24-point set would therefore meet every affine hyperplane in at most 17 labels. Evaluating its affine functionals gives a binary code of dimension 13 and minimum distance at least seven. Repeating one evaluation coordinate gives length 25, contradicting the previously checked code bound. [Quotient count](Green51ExteriorPair.lean) · [Evaluation bound](Green51AffineEvaluation.lean) · [Earlier 25-point theorem and coding-theory attribution](TWELVE-AFFINE-THRESHOLDS.md)

From the pinned Formal Conjectures checkout, set `notebook` to this repository's path and run `lake env python3 "$notebook/scripts/replay-research" Green51TwentyFourBounds`.
