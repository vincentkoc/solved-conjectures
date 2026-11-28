# Deletions that preserve an extremal double

Fix $s\ge1$ and $r\ge0$. In $\mathbb F_2^{2s+2+r}$, let $H$ consist of the vectors with at most $s$ ones in the first $2s+2$ coordinates. The remaining $r$ coordinates are free. The minimum number of points whose deletion can change $H+H$ is exactly
$$
d=\frac{2^r}{2}\binom{2s}{s}.
$$
Every subset obtained by fewer than $d$ deletions has the same double, even if its density falls below the interval where the earlier missing-count theorem applies. There is a set of exactly $d$ points whose deletion removes a specified direction with $2s$ active ones. For $r=0$, integrality follows from the pairing in that direction. [Deletion distance](Green51DeletionRadius.lean)

For example, take $s=6,r=2$. The cylinder has 25,904 points in dimension 16. After any 1,847 deletions, it still misses exactly the original 60 directions and contains a largest affine flat of dimension 14 in its double. Some 1,848 deletions change the double. The density-only guarantee for this particular double extended to 527 arbitrary deletions. [Sharp missing count](SHARP-MISSING-COUNT.md) · [Structure at equality](EXTREMAL-PERIODS.md)

For a fixed nonzero represented direction $z$, translation by $z$ partitions $H\cap(H+z)$ into disjoint pairs. To lose $z$, one must delete a point from every pair. Choosing one endpoint per pair suffices. This argument works for any finite binary input. [Direction-by-direction deletion cost](Green51DirectionDeletion.lean)

General formulas count intersections of two Hamming balls at any center distance. Here the deletion cost depends on the smallest positive overlap. [Exact Size of Intersections of Hamming Balls in Zqn](https://www.utupub.fi/items/1754155b-4676-4864-bdcd-0573e8459534)

Any represented direction has at most $2s$ active ones. Enlarge those active positions to a face on $2s$ coordinates and use the whole free factor. In the face the ball occupies half the points plus half the central layer. Inclusion–exclusion gives at least $2^r\binom{2s}{s}$ ordered representations of every direction in the double. In a direction with all $2s$ chosen coordinates active, the representations use exactly $s$ of them and none of the other active positions, attaining the bound. [Overlap bounds](Green51HammingOverlap.lean)

The result describes a particular family of witnesses for Green 51. The guaranteed dimension for arbitrary inputs remains open. [Pinned Green 51](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)
