# Counting affine classes of dense binary doubles

Let $g=2s+3$, $n=g+1$ and $s\ge5$. Consider the sumsets $S=A+A\subseteq\mathbb F_2^n$ whose largest affine subspace has dimension $n-2$, with $A$ of density greater than $\tfrac12-\binom{2s}{s}/2^{2s+1}$. The circuit carrier for the missing set has $g$ rows of four points. Write $k=|S^c|$ and $h=4g-k$ for the unused places in the carrier.

For $0\le h\le g$, the number $N(h)$ of classes under arbitrary ambient affine maps is independent of $g$. It equals the number of partitions of $h$ with parts in $\{1,2,3,4,6\}$. In particular, as $h\to\infty$ along any eligible sequence of dimensions,
$$
N(h)/h^4\longrightarrow 1/3456.
$$
At $h=2$ the two classes correspond to a pair of unused places in one row or two unused places in different rows. [Stable class number and limit](Green51AffineClassAsymptotic.lean)

### From rows to partitions

The [affine classification](DENSE-DOUBLE-AFFINE-EQUIVALENCE.md) records counts $a,c,d$ of rows of sizes one, three and four and an unordered triple $x\le y\le z$ of two-point row counts. Each singleton row leaves three places unused, each three-point row leaves one, and each pair leaves two. Thus
$$
h=c+3a+2(z-y)+4(y-x)+6x.
$$
These five nonnegative integers determine the profile. When $g\ge h$ there are enough rows for every such partition, with the remaining rows full. The Lean equivalence includes the case $h=0$. [Profile equivalence](Green51StableDefectPartitions.lean) · [Orbit quotient](Green51AffineProfileCount.lean)

For a finite bound, the non-unit multiplicities form a four-dimensional lattice simplex with weights $2,3,4,6$. Coordinate division with remainder places 144 ordinary lattice points in each box; their total weights differ from the box origin by at most 11. Stars and bars gives
$$
\binom{h+4}{4}\ \le\ 144\,N(h)\ \le\ \binom{h+15}{4}.
$$
Restricted partition functions and their leading terms are classical. The reduction of the affine classes to this particular function and both finite inequalities are checked in Lean. [Box bounds](Green51DefectClassGrowth.lean) · [Beck–Gessel–Komatsu](https://arxiv.org/abs/math/0306036)

### All twenty counts in dimension 16

The executable table also handles $h>g$ throughout the near-extremal range $4\min(5g+12,4g+20)<8k$. It accounts for the finite supply of rows. In dimension 16, $g=15$ and the generator condition is $|A|>25{,}376$. Each entry below is the cardinality of the quotient of the actual dense sumset family. [Finite enumeration](Green51AffineProfileTable.lean) · [Kernel-checked table](Green51AffineProfileExamples.lean)

| Missing points $k$ | Affine classes in increasing order of $k$ |
| --- | --- |
| 41–45 | 136, 123, 103, 91, 75 |
| 46–50 | 64, 51, 44, 33, 28 |
| 51–55 | 21, 17, 12, 10, 6 |
| 56–60 | 5, 3, 2, 1, 1 |

Green's general guaranteed-dimension question remains open. The pinned statistic uses the largest affine dimension contained in the double. [Pinned problem](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

From the pinned Formal Conjectures checkout, run `lake env python3 "$runner" Green51AffineProfileExamples Green51AffineClassAsymptotic` using the [notebook replay setup](../README.md#replay).
