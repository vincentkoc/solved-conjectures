# Affine three-spaces in twelve binary dimensions

Let \(A\subseteq\mathbb F_2^{12}\). Every 25-point set has an affine three-space in \(A+A\). An explicit 20-point set avoids all such spaces. The later fifteen-point section argument sharpens the forcing range to 21 through 24 inclusive. [Twenty-four-point bound](SIMPLEX-SECTION.md) For linear three-spaces through the origin the smallest forcing cardinality is 26. [Affine upper bound](Green51TwelveAffine.lean) · [Twenty-point example](Green51TwelveAffineWitness.lean) · [Linear threshold](TWELVE-DIMENSIONS.md)

For the guaranteed dimension \(F(12,\alpha)\) in Green's original question, the endpoints give the following exact values and bound. [Canonical density statements](Green51TwelveAffineBounds.lean) · [Pinned problem](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

| Density | Guaranteed dimension |
| --- | --- |
| \(2/4096<\alpha\le20/4096\) | Exactly 2 |
| \(24/4096<\alpha\le25/4096\) | Exactly 3, and a 25-point witness avoids every linear three-space |
| \(24/4096<\alpha\le1\) | At least 3 |

### The upper bound

Suppose the double of a 25-point set contains no affine three-space. At most 18 of its points can lie in any affine hyperplane, by the 19-point threshold in dimension eleven. Evaluate each affine linear functional on the 25 points. A nonconstant functional takes the value one at least seven times, and the nonzero constant functional has weight 25. Evaluation therefore embeds the 13-dimensional space of affine functionals in a binary code of length 25 and minimum distance at least seven. Appending the parity bit would give a binary \([26,13,8]\) code. The notebook proves the nonexistence bound which Brouwer's tables attribute to C. L. M. van Pul in 1985. [Hyperplane reduction](Green51FlatSections.lean) · [Eleven-dimensional threshold](ELEVEN-DIMENSION-THRESHOLDS.md) · [Parity extension](Green51AffineEvaluation.lean) · [Checked code bound](Green51TwelveCodes.lean) · [Grassl's tables and attribution](https://www.codetables.de/BKLC/BKLC.php?k=13&n=26&q=2)

### The lower bound

Read each integer as its twelve binary coordinates. Take zero, the twelve coordinate unit vectors, and the seven labels \(1719,3480,3753,378,3846,1738,2759\). For each nonempty subset of the seven extras, its size plus the Hamming weight of its sum exceeds six. This rules out zero sums of four or six distinct labels and excludes a linear three-space in the double. The total sum of all twenty labels is the sum of the two labels 8 and 2048. [Binary column check](Green51SystematicChecks.lean) · [Witness and total-sum criterion](Green51TwelveAffineWitness.lean)

An affine three-space would then require sixteen labels with sum zero. The four discarded labels would have the same sum as the pair. Their symmetric difference with the pair would be a zero-sum set of size two, four or six. Two distinct binary labels cannot sum to zero, and the column check excludes the other two sizes. This argument applies to any twenty-label set with the same short-relation and total-sum conditions. [Sixteen-label relation](Green51PairedTypes.lean)

From the pinned Formal Conjectures checkout, set `notebook` to this repository's path and run `lake env python3 "$notebook/scripts/replay-research" Green51TwelveAffineBounds`.
