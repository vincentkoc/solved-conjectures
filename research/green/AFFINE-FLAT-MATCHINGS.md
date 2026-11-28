# When an affine flat can occur without a linear three-space

Let \(A\) be a subset of a binary vector space and suppose \(A+A\) contains no three-dimensional linear subspace. If \(A+A\) contains an affine flat of dimension \(d\ge3\), then
\[
|A|\ge 2^{d+1}.
\]
Equality occurs for every \(d\ge3\). In dimension three both budgets are exact: sixteen labels in ten ambient coordinates suffice, and **every binary cube of dimension at most nine has the same three-space test for linear and affine flats**. In general the ambient dimension must be at least \(3d+1\), and \(3d+3\) suffices. [Least label count](Green51AffineMatchings.lean) · [Ambient dimension theorem](Green51TenDimensions.lean)

## Why the labels form a matching

A double containing an affine three-space has at least eight points, so \(A\) has at least five. By the four- and six-point criterion, the augmented columns \((1,a)\) have no nonzero kernel word of Hamming weight at most six. The affine flat misses zero, since otherwise it would be linear. Each of its points has a unique representative supported on two labels. [Short-relation criterion](SPARSE-THREE-SPACES.md)

Suppose two distinct representatives share a label. Their difference \(D\) has weight two and translates the flat to itself in the quotient. Under that translation, every representative changes by exactly \(D\): any discrepancy would be a kernel word of weight at most six. Consequently every representative has at most one coordinate outside the support of \(D\). The four words representing an affine parallelogram therefore sum to a kernel word supported on at most six coordinates, so every parallelogram lifts. This would lift the whole flat to a radius-two Hamming ball, whose affine flats have dimension at most two. Thus the \(2^d\) pairs use disjoint labels. [Matching argument](Green51AffineMatchings.lean) · [Hamming-ball dimension bound](Green50Sharp.lean)

## Simultaneous sharpness

Take the classical BCH graph \(x\mapsto(x,x^3,x^5)\) over \(K=\mathbb F_{2^m}\). Its \(2^m\) labels exclude a linear three-space in the double. The sums of the labels at \(x\) and \(x+1\) are a translate of the range of the binary linear map
\[
x\longmapsto(0,x^2+x,x^4+x).
\]
The kernel is \(\{0,1\}\), so this flat has dimension \(m-1\). Taking \(m=d+1\) attains the minimum label count. [Graph and derivative](Green51AffineSeparation.lean) · [Bose and Ray-Chaudhuri, 1960](https://doi.org/10.1016/S0019-9958(60)90287-4)

For \(m=4\), every \(x^5\) satisfies \((x^5)^4=x^5\) because \(x^{16}=x\). This puts the last coordinate in a subspace of dimension at most two. The three coordinates together need only \(4+4+2=10\) binary coordinates. On the lower-bound side, sixteen labels would require at least \(16+\binom{16}{3}=576\) distinct singleton and triple sums, more than fit in nine dimensions. The same counting argument with \(2^{d+1}\) labels gives the general \(3d+1\) lower bound. [Compression and packing](Green51TenDimensions.lean) · [Pinned Green 51](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)
