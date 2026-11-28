# Which directions can be missing from a dense binary sumset?

In dimension 16, take any set $D$ of 41 to 60 directions. There is a set $A$ of more than 25,376 points with $D=\mathbb F_2^{16}\setminus(A+A)$ if and only if every odd subset of $D$ summing to zero has at least 15 elements. This includes sets $D$ lying in an affine hyperplane. [Recognition theorem](Green51MissingMaskClassification.lean)

More generally, take $s\ge5$, $r\ge0$, $n=2s+2+r$, and $g=2s+3$. In the count range
$$
\min(5g+12,4g+20)2^r < 8|D|,\qquad |D|\le g2^r,
$$
the same equivalence holds with odd-girth bound $g$ and input density greater than $h_{2s}=\tfrac12-\binom{2s}{s}/2^{2s+1}$. When no linear functional takes the value one throughout $D$, the lower count bound alone suffices. The necessity comes from the odd-girth bound on missing directions. For sufficiency the stability theorem places $D$ inside a shortest circuit plus a complementary subspace. A linear change of coordinates identifies that construction with the directions missed by a Hamming ball times a full binary space. [Odd-girth stability](MISSING-STABILITY.md) · [Circuit equivalence](Green51CircuitEquivalence.lean)

Every subset $J$ of these $g2^r$ Hamming directions can be realized, including the empty set. Starting from the Hamming cylinder, at most three points are added and at most $3|J|$ are removed. The resulting double misses precisely $J$. Thus the dimension-16 cylinder realizes all $2^{60}$ subsets of its 60 missing directions at the stated density. [Hamming realization](Green51HammingMasks.lean)

The three new points cover the missing directions by translation. Their pairwise active-coordinate distances are at least three, so an old point removed for a forbidden direction cannot serve as the required partner for a different one. Deleting those partners preserves the original double by the exact deletion-distance bound. For a set of forbidden directions in the level-one coset of a linear functional, the construction instead inserts one point opposite its kernel. Alon and Zamir use this one-point construction, up to translation, in their proof of Theorem 7 on typical binary sumsets. Geelen gives the sharp odd-girth bound for binary matroids. [Three-point construction](Green51HammingCover.lean) · [Editing lemma](Green51MissingMaskEdits.lean) · [Deletion distance](HAMMING-DELETION-DISTANCE.md) · [Alon and Zamir](https://arxiv.org/abs/2403.16589) · [Geelen](https://arxiv.org/abs/1401.5769)
