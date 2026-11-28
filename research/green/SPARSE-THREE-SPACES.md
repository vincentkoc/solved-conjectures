# Three-dimensional subspaces in binary sumsets

Let \(A\subseteq\mathbb F_2^n\) have at least five elements. Its double \(A+A\) contains a three-dimensional **linear** subspace if and only if four or six distinct elements of \(A\) sum to zero. The largest size \(K(n)\) of a set avoiding such a subspace satisfies
\[
2^{\lfloor n/3\rfloor}\le K(n)\le 4\,2^{\lfloor n/3\rfloor}\qquad(n\ge3).
\]
In particular \(\log K(n)/n\to(\log 2)/3\). [Criterion and packing bound](Green51SparseDimensions.lean) · [Extremal function and limit](Green51SparseBounds.lean)

For Green's original **affine** guarantee \(F(n,\alpha)\), the checked bounds give
\[
F(n,\alpha)=2 \qquad
\left(n\ge4,\quad \frac{2}{2^n}<\alpha\le\frac{2^{\lfloor n/4\rfloor}}{2^n}\right).
\]
Three distinct points already put a plane through zero in the double. In the opposite direction, \(F(n,k/2^n)\ge3\) whenever \(5\le k\le2^n\) and \(k+\binom{k}{3}>2^n\). The transition between these bounds for an arbitrary affine three-space remains open here. [Affine bounds](Green51SparseBounds.lean) · [Pinned Green 51](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

## Why four or six points suffice

Choose four distinct points \(a,b,c,d\). If their sum is nonzero and lies in \(A+A\), the three differences \(a+b,a+c,a+d\) span a three-space there. A six-point relation gives exactly such a fourth-order sum. A four-point relation lets a fifth point replace one of the original four. The size hypothesis matters. A plane of four points doubles to itself.

Conversely, use binary parity-check columns \((1,a)\), one per point of \(A\). Without four- or six-point relations, every nonzero kernel word has Hamming weight greater than six. Each point of a linear subspace in \(A+A\) lifts, with first coordinate zero, to a word of weight at most two. The three words representing \(x,y,x+y\) sum to zero because their total weight is at most six and their syndrome is zero. Thus the lift is linear. A linear subspace of a radius-two Hamming ball has dimension at most two, by projection onto pivot coordinates. [Linear lifting proof](Green51SparseDimensions.lean)

## The scale of the bounds

In the absence of those relations, the sums over singletons and three-element subsets of \(A\) are all distinct. Counting them gives \(k+\binom{k}{3}\le2^n\). For the construction take zero and the classical BCH columns \((x,x^3,x^5)\) over \(\mathbb F_{2^m}\), with \(m=\lfloor n/3\rfloor\), and pad with zero coordinates. Their short-relation bound gives the matching linear avoidance exponent. Adding the coordinate \(x^7\) excludes kernel words through weight eight, which lets four representatives lift an affine parallelogram. This gives the affine example with \(m=\lfloor n/4\rfloor\). [Bose and Ray-Chaudhuri, 1960](https://doi.org/10.1016/S0019-9958(60)90287-4) · [Binary parity-check construction](Green50BCH.lean) · [Affine flat lifting](SPARSE-SUMSET-OBSTRUCTIONS.md)
