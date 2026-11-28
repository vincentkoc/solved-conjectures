# Counting distinct dense sumsets near the maximum missing count

In dimension 16, about $2.598\times10^{140}$ distinct sumsets $A+A$ miss exactly 41 directions and admit an input with $|A|>25{,}376$. Of these, exactly
$$
28\,695\,069\,593\,324\,713\,072\,606\,999\,769\,402\,841\,169\,720\,190\,563\,177\,645\,847\,462\,610\,468\,864\,000
$$
have largest affine dimension 14. Each other sumset contains a hyperplane. The count is over subsets of the labelled cube. Different inputs can give the same sumset. [Exact total](Green51CompleteSumsetCount.lean) · [Codimension-two count](Green51DenseSumsetEnumeration.lean)

Take $s\ge5$, $r\ge0$, $n=2(s+1)+r$, $g=2s+3$, and $\ell=2^r$. Let $N_k$ count distinct doubles in dimension $n$ missing $k$ points, having largest affine dimension $n-2$, and admitting an input of density greater than $\tfrac12-\binom{2s}{s}/2^{2s+1}$. Whenever $8k>\ell\min(5g+12,4g+20)$,
$$
N_k = \frac{\prod_{i=0}^{g-2}(2^n-2^i)}{g!}
       \sum_{j=0}^g (-1)^j\binom gj\binom{(g-j)\ell}{k}.
$$
The formula gives zero for $k>g\ell$. In the example, each circuit frame contains 1,807,312,363,852,800 eligible 41-subsets. [Frame partition](Green51SectionPartition.lean) · [Arithmetic and original sumset predicate](Green51DenseSumsetEnumeration.lean)

A frame consists of the $g$ points of a shortest odd circuit, each enlarged to a coset of the same complementary subspace. The stability theorem gives each eligible missing set a unique frame. More than half its points are present, so any functional constant on the missing set vanishes on the period subspace. Hitting every circuit coset rules out a functional constantly one. The complement then has largest affine dimension exactly $n-2$. Missing an entire coset gives dimension $n-1$. Inclusion–exclusion over the $g$ cosets gives the sum in the formula. [Majority sections](Green51FrameSections.lean) · [Affine dimension](Green51SectionDimension.lean)

To count the frames, choose a surjection onto a binary cube of dimension $g-1$ with a fixed spanning circuit. Its inverse image of that circuit is a frame. Every frame arises, and each bijection between its circuit and the reference circuit specifies one surjection. This gives the factor $g!$. The ordered independent rows of the surjection give the product in the numerator. [Quotient maps](Green51FrameQuotients.lean) · [Frame count](Green51CircuitFrameCount.lean)

To include the hyperplane cases, let $B(n,k)$ count the $k$-subsets of the cube contained in some level-one hyperplane. For $k>0$,
$
B(0,k)=0,\qquad B(n+1,k)=(2^{n+1}-1)\left[\binom{2^n}{k}-B(n,k)\right].
$
When $k\le g\ell$ as well as satisfying the lower bound above, the complete sumset count is $B(n,k)+N_k$. To see the recurrence, mark a point $a$ of a $k$-set and translate the set by $a$, obtaining a set $E$ containing zero. The original set lies in a level-one hyperplane exactly when $a$ is outside the linear span of $E$. A span of size $w$ in dimension $n+1$ has $2^{n+1}/w-1$ nonzero annihilating functionals. Weight each by $w$ and count inside their kernels to obtain the recurrence. [Rooted subsets](Green51RootedAffineSets.lean) · [Affine count](Green51AffineCount.lean) · [Sumset count](Green51CompleteSumsetCount.lean)

Geelen proved the sharp odd-girth bound for binary matroids. Alon and Zamir proved an asymptotic count for all binary sumsets and showed that almost all contain a linear hyperplane. Here the input density, missing cardinality, and largest affine dimension are all prescribed. Green’s general question about the largest guaranteed affine dimension remains open. [Geelen](https://arxiv.org/abs/1401.5769) · [Alon and Zamir](https://arxiv.org/abs/2403.16589) · [Missing-direction recognition](PRESCRIBED-MISSING-DIRECTIONS.md)
