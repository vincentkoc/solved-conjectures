# How many directions can a double miss?

Let $h_{2s}=\tfrac12-\binom{2s}{s}/(2\cdot4^s)$. Take $s\ge1$, $r\ge0$ and $n=2s+2+r$. Suppose $h_{2s}<\alpha\le h_{2s+2}$. Among all $A\subseteq\mathbb F_2^n$ of density at least $\alpha$ for which $A+A$ contains no affine hyperplane, the largest possible number of missing vectors is
$$
\max_A \bigl|\mathbb F_2^n\setminus(A+A)\bigr|=(2s+3)2^r.
$$
Equivalently, the sharp missing fraction is $(2s+3)/2^{2s+2}$, independent of the extra dimension $r$. For example, in dimension sixteen and for minimum sizes from 25,377 through 25,904, the maximum is 60. The general guaranteed affine dimension remains open. [Extremal theorem](Green51MissingCount.lean) · [Pinned Green 51](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

## Upper bound

Write $D=\mathbb F_2^n\setminus(A+A)$. Above $h_{2s}$, every odd subset of $D$ that sums to zero has at least $2s+3$ elements. If a linear functional took the value one on all of $D$, its kernel would lie in $A+A$. Thus $D$ is nonaffine in the binary-matroid sense. Geelen's Theorem 1.1 bounds its size by $(2s+3)2^{n-2s-2}$. The Lean proof derives this finite-vector-space bound directly. [Density and odd relations](Green51LogDensityWindow.lean) · [Binary odd-girth bound](Green51GeelenGirth.lean) · [Geelen, Theorem 1.1](https://arxiv.org/abs/1401.5769)

To count $D$, choose a shortest odd circuit $C$ and extend $C$ with one point removed to a basis of the ambient space. Fix the coordinates outside the circuit span. The missing vectors in that slice are represented by subsets of $C$ of one parity at pairwise Hamming distance at most two. Translating one word to the empty set leaves a pairwise intersecting family of edges. Such a family is a star or has at most three edges, so the slice has at most $|C|$ words. Summing over the outside coordinates gives the bound. [Slice bound and its equality case](Green51DiameterTwoSlices.lean)

## Attainment

Take the ball of radius $s$ in the first $2s+2$ coordinates and allow all remaining $r$ coordinates. Its density is $h_{2s+2}$. Its double misses exactly the two heaviest layers of the first cube, at every value of the extra coordinates. These missing vectors meet both sides of every affine hyperplane partition, so the double contains no hyperplane. Geelen's Theorem 4.2 constructs sharp binary matroids by doubling an odd circuit. Here the Hamming cylinder realizes those missing directions as the complement of an actual double at the required density. [Hamming cylinder](Green51ThresholdExample.lean) · [Geelen, Section 4](https://arxiv.org/pdf/1401.5769#page=7)
