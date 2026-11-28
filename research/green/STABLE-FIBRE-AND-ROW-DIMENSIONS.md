# Stabilization of the affine class count in both dimensions

Write $g=2s+3$, $n=g-1+r$ and $s\ge5$. Consider dense doubles $S=A+A\subseteq\mathbb F_2^n$ whose largest contained affine subspace has dimension $n-2$, where $A$ has density greater than $\tfrac12-\binom{2s}{s}/2^{2s+1}$. Prescribe $|S^c|=g2^r-h$, so $h$ counts unused places in the missing-set carrier.

If $g\ge h$, $2^r>h$ and $r\ge h-1$, the number of ambient affine equivalence classes depends only on $h$. The universal finite model has $h$ rows in $\mathbb F_2^{h-1}$ with a total of $h$ marked sites. Two configurations agree up to row permutation, independent translations of the rows and one common invertible linear map of the fibre. When $h=0$ the model has one empty configuration. [Stable class number](Green51UniversalDefectNumber.lean)

### Why the two dimensions stabilize

Choose one marked point as origin in every nonempty row. A row with $j$ points contributes at most $j-1$ vectors to the common span of differences. Its dimension is at most $h-1$ for $h>0$. A linear isomorphism of finite-dimensional subspaces extends to the ambient space. It follows that every larger-space configuration can be moved into a fibre of dimension $h-1$. [Common span](Green51OmissionSpan.lean) · [Compression](Green51StableFibreRank.lean)

Enlarging the fibre also preserves distinctions between configurations. For fixed labels, take the linear map sending formal coefficients to linear combinations of within-row differences. Its kernel determines the configuration up to the common linear change and independent translations. An injective embedding preserves this kernel, and allowing row and site permutations on both sides preserves the equivalence. [Difference kernels](Green51RowDifferenceKernels.lean) · [Unlabelled configurations](Green51WordEmbeddings.lean)

Once there are $h$ rows, each further row can be empty. Adding an empty row increments the same translation-class count for either family. Conversely, a family with $h$ sites in more than $h$ rows has an empty row to remove. Taking row complements recovers the [classification of actual dense doubles](DENSE-DOUBLE-FIBRE-CLASSES.md). The hypothesis $h<2^r$ guarantees that every row in the missing set remains occupied. [Empty rows](Green51EmptyRowStability.lean) · [Original sumset quotient](Green51DenseFibreStability.lean)

### Small configurations

The following computations are separate from the Lean stabilization theorem. They compare the four-point calculation, the eight-point calculation and the universal model.

| Unused places $h$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Four-point fibres, 15 rows | 1 | 1 | 2 | 3 | 5 | 6 | 10 | 12 | 17 |
| Eight-point fibres, 15 rows | 1 | 1 | 2 | 3 | 7 | 10 | 21 | 33 | 65 |
| Universal model | 1 | 1 | 2 | 3 | 7 | 11 | 27 | 53 | 142 |

To reproduce the universal row, partition the $h$ site labels into $b$ nonempty rows and choose one anchor in each. Enumerate subspaces of $\mathbb F_2^{h-b}$ as kernels of the map on the other site differences. Exclude a kernel when two positions in the same row have equal images. Act on the remaining kernels by permutations within rows and exchanges of equal-sized rows, and sum the orbit counts over the partitions. Requiring kernel codimension at most $r$ and row size strictly below $2^r$ also recovers the two finite-fibre rows above. The four-point numbers agree with the [verified dimension-16 table](STABLE-AFFINE-CLASS-COUNTS.md).

Green's general guaranteed-dimension problem remains open. The use of a common linear action and column permutations is classical in representations of binary linear codes. Here one must also account for the row translations and relate the finite configurations to the original dense doubles. [Codes and projective multisets](https://research.tue.nl/files/1331813/Metis117555.pdf) · [Pinned Green 51](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

From the pinned Formal Conjectures checkout, run `lake env python3 "$runner" Green51UniversalDefectNumber` using the [notebook replay setup](../README.md#replay).
