# Affine flats in doubles of binary BCH columns

Let \(K=\mathbb F_{2^m}\), \(C(x)=(x,x^3,x^5)\), and \(S\subseteq K\). For every \(d\ge3\), the double \(C(S)+C(S)\) contains an affine binary \(d\)-flat if and only if \(S\) contains an affine \((d+1)\)-flat. The full curve uses \(3m\) binary coordinates for \(2^m\) distinct labels. The earlier quadratic-matrix construction gives the same equivalence in a larger space. [BCH inverse theorem](Green51BCHInverse.lean) · [Quadratic-matrix theorem](QUADRATIC-IMAGE-FLATS.md)

For \(|S|\ge3\), let \(D(S)\) be the largest dimension of an affine binary subspace in \(S\). Then
\[
 D(C(S)+C(S))=\max\{2,D(S)-1\}.
\]
Any three labels supply the plane consisting of zero and their three pair sums. For the full field with \(m\ge4\), the exact dimension is \(m-1\). The formal statement uses the pinned Green 51 definition of `maxCosetDim`. [Dimension formula](Green51BCHDimensions.lean) · [Pinned question](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

## Why the first coordinate is constant

Write \((a,b,c)=C(x)+C(y)\). In characteristic two, \(ac=a^6+a^3b+b^2\), so \(a^7=a^2c+a^4b+ab^2\). The right side is quadratic over \(\mathbb F_2\), and its third additive difference vanishes on any affine three-space of such sums. For the left side that difference is the product of the seven nonzero binary linear combinations of the three first-coordinate increments. Hence the projection of a flat in the double onto the first coordinate has rank at most two. [Secant identity and third difference](Green51BCHDirections.lean)

Suppose a flat contains a displacement with first coordinate \(a\ne0\) and a nonzero vertical displacement \((0,v,w)\). Over a basepoint with first coordinate \(t\), the four corners of the resulting rectangle force \(v=t(t+a)a\) and \(w=(t^2+ta+a^2)v\). Thus there is at most one nonzero vertical displacement, and the flat has at most two distinct first coordinates. Such a flat has at most four points. Any affine flat of dimension at least three therefore lies over one first coordinate \(t\), necessarily nonzero since the fiber at zero consists of zero alone. [Constant-coordinate theorem](Green51BCHDirections.lean)

On that fiber the map \(x\mapsto C(x)+C(x+t)\) is affine. Its linear part is \(x\mapsto(0,tx^2+t^2x,tx^4+t^4x)\), with kernel \(\{0,t\}\). A represented point has exactly the pair of preimages \(x,x+t\), so the preimage of a represented \(d\)-flat is a \((d+1)\)-flat contained in \(S\). In the other direction, take any nonzero direction \(t\) of a \((d+1)\)-flat in \(S\). Its image under the same map is a \(d\)-flat in the double. [Kernel and both preimages](Green51BCHInverse.lean)

The coordinates are the classical binary triple-error-correcting BCH columns. Charpin and Zinoviev study their syndromes and coset weights for odd extension degree in §4. The statements here concern affine subspaces in doubles of arbitrary subsets of columns and hold in both parities. [Bose and Ray-Chaudhuri](https://doi.org/10.1016/S0019-9958(60)90287-4) · [Charpin and Zinoviev](https://doi.org/10.1137/S089548019529443X)

To replay the proof, run `lake env python3 /path/to/solved-conjectures/scripts/replay-research Green51BCHDimensions` from the pinned formal-conjectures checkout. The runner rebuilds the notebook dependencies and kernel-checks each module separately.
