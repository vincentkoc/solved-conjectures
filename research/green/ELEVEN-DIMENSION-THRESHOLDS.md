# Affine and linear three-spaces in eleven binary dimensions

For \(A\subseteq\mathbb F_2^{11}\), **19 points force an affine three-space in \(A+A\)**, and **25 force a linear three-space**. Both thresholds are sharp. In the original density formulation, for \(\alpha\le1\),
\[
3\le\operatorname{guaranteedMaxCosetDim}(11,\alpha)
\quad\Longleftrightarrow\quad 18/2048<\alpha.
\]
The guaranteed dimension equals two for \(2/2048<\alpha\le18/2048\) and three for \(18/2048<\alpha\le24/2048\). Green's general density problem remains open. [Thresholds and plateaus](Green51ElevenThresholds.lean) · [Pinned Green 51](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

## Why nineteen points suffice

Suppose a double contains no affine three-space. The augmented parity-check matrix has columns \((1,a)\) for \(a\in A\). All its relations have even weight. A relation of weight four or six would give a linear three-space. A relation of weight sixteen would also give an affine three-space. On its sixteen labels the check kernel has dimension at least four and contains the all-ones vector. Every other nonzero word has weight eight, as does its complement. Three independent rows vanishing on one coordinate partition the labels into eight pairs. Their pair sums form the required affine space. [Sixteen-label argument](Green51ElevenRelations.lean) · [Pair partition](Green51Hadamard.lean)

Take \(|A|=19\). Every sixteen labels span the full augmented space, since sixteen points in an affine hyperplane already force a three-space by the dimension-ten theorem. The kernel therefore has dimension seven. Deleting any three columns leaves the check surjective, so projection of the kernel onto any three coordinates is uniform. Double-counting subsets of one, two and three nonzero coordinates gives the binomial moments of the weight distribution. [Hyperplane argument](Green51ElevenColumns.lean) · [Projection and nineteen-point theorem](Green51NineteenLabels.lean) · [Pless on weight moments](https://www.sciencedirect.com/science/article/pii/S001999586390189X)

| Weight | 0 | 8 | 10 | 12 | 14 | 18 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Count forced by the moments | 1 | 75 | 10 | 36 | 6 | 0 |

Exactly sixteen words would have weight two modulo four. On the even kernel the parity of half the weight is a quadratic function. A nonzero binary quadratic function on 128 points takes the value one at least 32 times. This contradiction rules out the hypothetical double. [Moment calculation](Green51NineteenMoments.lean) · [Quadratic support bound](Green51ElevenQuadratic.lean)

## Sharp witnesses

The 24-point set comes from the extended binary Golay code. The coordinates use the cyclic generator \(x^{11}+x^9+x^7+x^6+x^5+x+1\), followed by parity extension. Shortening at the first six cyclic coordinates gives the 18-point example. The Lean certificate uses the resulting explicit lists of labels and checks their subset sums directly. For comparison, Östergård determined the unrestricted coding maxima \(A(18,8)=64\) and \(A(19,8)=128\). [Generator polynomial](https://www.iaeng.org/publication/IMECS2008/IMECS2008_pp1191-1193.pdf) · [Östergård's paper](https://acris.aalto.fi/ws/portalfiles/portal/27672730/ELEC_ostergord_golay.pdf) · [Witness coordinates and checks](Green51GolayWitnesses.lean)

Neither label set has a four- or six-point zero sum. In the 18-point set the total, encoded as an eleven-bit integer, is 934. No pair sums to 934, so no sixteen labels sum to zero. Conversely, in any double avoiding linear three-spaces, an affine three-space uses sixteen distinct labels with zero total. This proves affine avoidance for the smaller witness. For the linear upper bound, all single-label and three-label sums must be distinct under avoidance. At 25 labels they already exceed the 2048 ambient points. [Affine relation](Green51PairedTypes.lean) · [Triple packing](Green51SparseDimensions.lean)

From the pinned Formal Conjectures checkout, set `notebook` to this repository’s path and run `lake env python3 "$notebook/scripts/replay-research" Green51ElevenThresholds`.
