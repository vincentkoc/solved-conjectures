# Dimension of the unused sites within the circuit rows

For a presentation of a dense binary double, form the vector space spanned by \(x-y\) over pairs of unused sites \(x,y\) in the same row. Write \(d\) for its dimension and \(h\) for the total number of unused sites. In the stable range, \(d\) concentrates near \(h/2\) when each affine class of doubles receives equal weight.

Suppose \(s\ge5\), \(10\le h\le 2s+3\), \(h<2^r\), and \(r\ge h-1\). Fix a spanning circuit of size \(2s+3\) in the base space. For every nonnegative integer \(D\) satisfying \(D^2\ge64h(\lfloor\log_2 h\rfloor+2)\), the fraction of affine classes admitting a presentation with \(|2d-h|\ge D\) is at most \(2^{-\lfloor D^2/8\rfloor}\). The representative and its coordinates can vary. The doubles are the actual sets \(A+A\) with the density threshold, missing-set size and maximal coset dimension in the [stable class theorem](STABLE-FIBRE-AND-ROW-DIMENSIONS.md). [Class bound](Green51DenseDirectionRank.lean)

For example, at \(h=2^{20}\) one can take \(D=40000\). In all but a fraction \(2^{-200000000}\) of classes, every presentation has \(504288<d<544288\). The [row-count bound](CONCENTRATION-OF-UNUSED-SITES.md) measures how many rows contain unused sites. Here the dimension measures how many independent binary directions those rows use together.

### How many classes fit into a smaller fibre?

Write \(N(h)\) for the stable number of classes and \(N_r\) for the count of actual doubles in fibre dimension \(r\). Under the same bound on \(D\), with \(h<2^r\) and \(s\ge5\), the following estimates apply even when \(r<h-1\).

| Fibre dimension | Fraction of stable classes |
| --- | --- |
| \(2r+D\le h\) | \(N_r/N(h)\le 2^{-\lfloor D^2/8\rfloor}\) |
| \(2(r+1)\ge h+D\), with at least \(h\) carrier rows | \(1-2^{-\lfloor D^2/8\rfloor}\le N_r/N(h)\le1\) |

The first estimate holds for any number of carrier rows \(2s+3\). For the second, translate one unused site per incomplete row to zero. If the common direction space has dimension at most \(r\), all rows then fit in one \(r\)-dimensional fibre. Enlargement preserves inequivalence, so the classes lost in the smaller fibre all have higher rank. At \(h=2^{20}\) and \(D=40000\), the first estimate applies through \(r=504288\) and the second from \(r=544287\). [Compression](Green51CompressDirectionRank.lean) · [Smaller fibres](Green51LowDimensionCount.lean) · [Upper range and monotonicity to the stable count](Green51FibreTransition.lean)

### Counting at fixed dimension

If \(b\) rows have unused sites, choosing an origin in each of them leaves \(m=h-b\) difference vectors. They span exactly the direction space defined above. For a prescribed rank \(d\le m\), the number of inequivalent configurations is at most
\[
b^m\,2^{(m-d)d+(m-d)}.
\]
The labels record a row assignment and a subspace of dimension \(m-d\), the kernel of the linear map on the difference vectors. A common change of binary coordinates and a separate translation in each row suffice to match two identical records. This estimate works for any finite-dimensional binary fibre. [Direction space](Green51RowDirectionSpace.lean) · [Kernel count](Green51MarkedSpanRank.lean) · [Fixed-rank bound](Green51FixedRankRows.lean)

The identity \(4d(h-d)=h^2-(2d-h)^2\) gives the loss away from the middle dimension. Summing over the at most \((h+1)^2\) choices of \(b,d\) and comparing with the [lower bound for the total number of classes](GROWTH-OF-STABLE-AFFINE-CLASSES.md) proves the stated inequality. Counting binary subspaces by dimension is classical. Green's general guaranteed-dimension question remains open. [Finite estimate](Green51DirectionRankBudget.lean) · [Sum over dimensions](Green51DirectionRankTail.lean) · [Wild, *The asymptotic number of binary codes and binary matroids*](https://arxiv.org/abs/cs/0408011) · [Pinned problem](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

From the pinned Formal Conjectures checkout, run `lake env python3 "$runner" Green51FibreTransition` using the [notebook replay setup](../README.md#replay).
