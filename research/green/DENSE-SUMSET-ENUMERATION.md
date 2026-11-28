# Counting distinct dense sumsets near the maximum missing count

In the binary cube of dimension 16, exactly
$$
28\,695\,069\,593\,324\,713\,072\,606\,999\,769\,402\,841\,169\,720\,190\,563\,177\,645\,847\,462\,610\,468\,864\,000
$$
distinct sumsets $S=A+A$ miss 41 points, have largest affine subspace of dimension 14, and admit an input $A$ with more than 25,376 points. The count is over subsets of the labelled cube. Different inputs can give the same $S$. [Enumeration theorem](Green51DenseSumsetEnumeration.lean)

Take $s\ge5$, $r\ge0$, $n=2(s+1)+r$, $g=2s+3$, and $\ell=2^r$. Let $N_k$ count distinct doubles in dimension $n$ missing $k$ points, having largest affine dimension $n-2$, and admitting an input of density greater than $\tfrac12-\binom{2s}{s}/2^{2s+1}$. Whenever $8k>\ell\min(5g+12,4g+20)$,
$$
N_k = \frac{\prod_{i=0}^{g-2}(2^n-2^i)}{g!}
       \sum_{j=0}^g (-1)^j\binom gj\binom{(g-j)\ell}{k}.
$$
The formula gives zero for $k>g\ell$. In the example, each circuit frame contains 1,807,312,363,852,800 eligible 41-subsets. [Frame partition](Green51SectionPartition.lean) · [Arithmetic and original sumset predicate](Green51DenseSumsetEnumeration.lean)

A frame consists of the $g$ points of a shortest odd circuit, each enlarged to a coset of the same complementary subspace. The stability theorem gives each eligible missing set a unique frame. More than half its points are present, so any functional constant on the missing set vanishes on the period subspace. Hitting every circuit coset rules out a functional constantly one. The complement then has largest affine dimension exactly $n-2$. Missing an entire coset gives dimension $n-1$. Inclusion–exclusion over the $g$ cosets gives the sum in the formula. [Majority sections](Green51FrameSections.lean) · [Affine dimension](Green51SectionDimension.lean)

To count the frames, choose a surjection onto a binary cube of dimension $g-1$ with a fixed spanning circuit. Its inverse image of that circuit is a frame. Every frame arises, and each bijection between its circuit and the reference circuit specifies one surjection. This gives the factor $g!$. The ordered independent rows of the surjection give the product in the numerator. [Quotient maps](Green51FrameQuotients.lean) · [Frame count](Green51CircuitFrameCount.lean)

Geelen proved the sharp odd-girth bound for binary matroids. Alon and Zamir proved an asymptotic count for all binary sumsets and showed that almost all contain a linear hyperplane. Here the input density, missing cardinality, and largest affine dimension are all prescribed. Green’s general question about the largest guaranteed affine dimension remains open. [Geelen](https://arxiv.org/abs/1401.5769) · [Alon and Zamir](https://arxiv.org/abs/2403.16589) · [Missing-direction recognition](PRESCRIBED-MISSING-DIRECTIONS.md)
