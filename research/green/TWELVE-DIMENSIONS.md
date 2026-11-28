# The three-space threshold in twelve binary dimensions

Every set of 26 points in \(\mathbb F_2^{12}\) has a three-dimensional linear subspace in its sumset \(A+A\). There is a set of 25 points for which \(A+A\) contains no such subspace. The theorem concerns a subspace through zero. Green's original question allows affine translates. [Sharp threshold](Green51TwelveThreshold.lean) · [Pinned Green 51 statements](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

For the upper bound, use the binary columns \((1,a)\) with \(a\in A\). If \(A\) avoids a linear three-space in its double, the columns have no four- or six-point relation. Distinctness excludes a relation of weight two, and the first coordinate excludes odd weights. With 26 columns, the kernel would have dimension at least 13 and minimum distance at least eight. For the lower bound, place the 24-label Golay example in a hyperplane and add one point outside it. The new coordinate keeps that point out of every zero-sum relation. [Short-relation criterion](Green51SparseDimensions.lean) · [Golay example](Green51GolayWitnesses.lean)

## A coding criterion in all dimensions

For \(n\ge4\), an avoiding set of \(n+1\) labels exists in \(\mathbb F_2^d\) if and only if there is a binary linear code of length \(n\), redundancy at most \(d\) and minimum distance at least seven. In the forward direction, puncture the even code obtained from the augmented labels at any one coordinate. Conversely, take the images of the \(n\) coordinate vectors in the code quotient and adjoin zero. Distance seven makes the images distinct and nonzero, and rules out a four- or six-label relation. This identifies the finite geometric threshold with the classical triple-error-correcting code existence problem in every dimension. [Equivalence in Lean](Green51TwelveThreshold.lean)

## The binary code bound

Brouwer's tables credit the nonexistence of a binary \([26,13,8]\) code to C. L. M. van Pul (private communication, 1985). The notebook proves the bound directly. Replacing a coordinate by the parity of the other coordinates preserves the dimension and the lower bound of eight on distance. It suffices to consider an even code. [Grassl's code tables and attribution](https://www.codetables.de/BKLC/BKLC.php?k=13&n=26&q=2) · [Lean proof](Green51TwelveCodes.lean)

Suppose first that the code contains a word of weight ten. Restrict all codewords to the other sixteen positions. The kernel has dimension one, since two nonzero words supported on those ten positions cannot have disjoint supports. Every nonzero restricted word has weight at least three. The radius-one Hamming balls around the restricted codewords would therefore occupy at least \(2^{12}\cdot17>2^{16}\) points.

If there is no word of weight ten, a word of weight fourteen would give a surjective restriction to the other twelve positions. Lifting a word of weight two there gives two nonzero even words whose weights sum to eighteen. One would have weight ten. Every word of weight above fourteen splits into smaller nonzero words with disjoint supports by rank-nullity. This excludes weights 18, 22 and 26, leaving only multiples of four. A doubly even code lies in its dual, and the all-ones word belongs to the dual alone at length 26. The identity \(|C||C^\perp|=2^{26}\) now forces \(\dim C\le12\). [Binary weight transform](Green51WeightTransform.lean)

From the pinned Formal Conjectures checkout, set `notebook` to this repository's path and run `lake env python3 "$notebook/scripts/replay-research" Green51TwelveThreshold`.
