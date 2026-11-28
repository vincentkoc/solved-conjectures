# Completing 18–23 labels in eleven binary dimensions

Let \(A\subseteq\mathbb F_2^{11}\), and suppose \(A+A\) contains no three-dimensional linear subspace. Every such set with at least 18 labels is contained in an avoiding 24-label set. From 19 labels onward the completion is unique in the original ambient space, with every existing label fixed. At 18 labels there can be two completions. The distinction is whether sixteen labels of \(A\) sum to zero. Both cases occur. [Completion theorem](Green51ShortenedCompletions.lean) · [Examples and flat counts](Green51ShortenedFlatCounts.lean)

| Labels in \(A\) | Zero-sum sixteen-sets | Possible next labels | 24-label completions | Affine three-spaces in \(A+A\) |
| ---: | ---: | ---: | ---: | ---: |
| 18 | 0 | 6 | 1 | 0 |
| 18 | 1 | 12 | 2 | 15 |
| 19 | 1 | 5 | 1 | 15 |
| 20 | 5 | 4 | 1 | 75 |
| 21 | 21 | 3 | 1 | 315 |
| 22 | 77 | 2 | 1 | 1,155 |
| 23 | 253 | 1 | 1 | 3,795 |
| 24 | 759 | 0 | 1 | 11,385 |

## Counting extensions

Augment each label \(a\) to the binary column \((1,a)\). A nonzero kernel word then selects an even zero-sum subset. Linear three-space avoidance gives minimum weight eight. If ten labels sum to zero, choosing subsets of nine of them produces 512 different syndromes. These syndromes and their separate translates by each outside column are disjoint. The space of 4,096 syndromes leaves room for at most seven outside labels. At length at least 18 this excludes weight ten. The remaining possible weights below length 24 are 0, 8, 12 and 16. [Ten-label packing](Green51ResidualPacking.lean) · [Other excluded weights](Green51MissingLabel.lean)

Shortening the kernel to seventeen positions leaves dimension at most five, by the first two character moments. Rank-nullity then gives dimension \(n-12\) before shortening, and every restriction to \(n-17\) coordinates is surjective. In particular the dual has no nonzero word of weight at most \(n-17\). The binary MacWilliams identity determines the short dual weights and the number of dual words of weight \(3\bmod 4\). Lean checks the transform over a general commutative ring and evaluates its integer coefficients for these six lengths. [Projection theorem](Green51CoordinateStrength.lean) · [Weight transform](Green51WeightTransform.lean) · [Weight profiles](Green51ShortenedProfiles.lean)

A candidate new label is the syndrome of an odd word. Its whole kernel coset must have weight \(3\bmod 4\), since adjoining the new column gives a relation of weight divisible by four. These cosets are represented by precisely the dual words of weight \(3\bmod 4\). A coset in this family admits the new label exactly when it contains no word of weight three. Two distinct triples have different syndromes by the minimum distance. Counting the resulting cosets gives the third column of the table. Finally, a 24-label completion supplies exactly \(24-n\) next labels, and counting these incidences gives the number of distinct completions. [Fibre count](Green51ExtensionFibres.lean)

## Relation to the coding literature

Dodunekov and Encheva classified the linear codes with parameters \([n,n-12,8]\) for \(18\le n\le23\). They found two equivalence classes at length 18 and one at each larger length, all obtained by shortening the extended binary Golay code. Östergård later proved the unrestricted size bounds \(A(18,8)=64\) and \(A(19,8)=128\). The arguments above independently count literal completions of the given labels and affine three-spaces in their doubles. The ambient dimension is fixed at eleven. [Dodunekov and Encheva (1993)](https://www.mathnet.ru/eng/ppi162) · [Östergård](https://doi.org/10.1007/s10623-018-0532-z) · [Pinned Green 51 statements](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

From the pinned Formal Conjectures checkout, set `notebook` to this repository’s path and run `lake env python3 "$notebook/scripts/replay-research" Green51ShortenedFlatCounts`.
