# Affine dimensions in a projected binary BCH double

Let \(K\) be the field of \(2^m\) elements, \(L\) a binary linear map, and \(A_L\) the image of \(x\mapsto(x,x^3,x^5,L(x^7))\). An affine \(d\)-space in \(A_L+A_L\), for \(d\ge3\), requires \(\dim\ker L\ge d\). For every proper divisor \(d\ge3\) of \(m\) and every \(0\le r\le m\), **some** kernel of dimension \(r\) gives such a flat if and only if \(d\le r\). In particular, over the 64-element field there are both three-dimensional kernels that give a three-flat and three-dimensional kernels that avoid all three-flats. [Dimension bound](Green51BCHFlatDimensions.lean) · [Attainable ranks](Green51BCHDimensionBounds.lean) · [Avoiding example in dimension six](EXCEPTIONAL-BCH-PROJECTION.md)

For \(m>0\) and \(0\le r\le m\), this construction places \(2^m\) labels in \(4m-r\) binary coordinates. Every affine flat in their double has dimension at most \(\max(2,r)\). Thus the pinned Green 51 guarantee at density \(\alpha\le 2^m/2^{4m-r}\) is at most \(\max(2,r)\). For example, 4,096 labels fit in dimension 44 with no five-dimensional affine subspace in their double. The general problem remains open. [Host theorem](Green51BCHDimensionBounds.lean) · [Pinned definition](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

## Dimension carried by the pair brackets

Write \(B(x,y)=xy(x+y)\). For a binary subspace \(V\subseteq K\) of dimension \(d\ge3\), the span of all \(B(x,y)\) for \(x,y\in V\) has dimension at least \(d\). For each nonzero \(x\in V\), the map \(y\mapsto B(x,y)\) has kernel \(\{0,x\}\), so its image has dimension exactly \(d-1\). If the total span had dimension below \(d\), all these images would coincide.

Put \(N=|V|=2^d\) and \(P=\prod_{v\in V\setminus\{0\}}v\). Translation by \(x\) permutes \(V\setminus\{0,x\}\), giving
\[
 \prod_{y\in V\setminus\{0,x\}}B(x,y)=x^{N-4}P^2.
\]
Each nonzero image value occurs exactly twice. If the image were independent of \(x\), then all \(N-1\) nonzero inputs would satisfy \(x^{N-4}=c\) for a single \(c\). This exceeds the degree of that nonconstant polynomial. [Product proof](Green51BracketProducts.lean)

This dimension obstruction is also consistent with Nyberg's bound on perfectly nonlinear binary maps. If the bracket image spanned only \(d-1\) dimensions, one could subtract a linear map from \(x\mapsto x^3\) on \(V\) to put its image in that span. Each nonzero derivative would take every one of the \(2^{d-1}\) output values twice, while Nyberg's bound gives output dimension at most \(d/2\). The Lean proof uses the displayed field product directly. [Nyberg, *Perfect Nonlinear S-Boxes*](https://doi.org/10.1007/3-540-46416-6_32)

A flat of dimension \(d\ge3\) gives a nonzero difference \(t\) and a \((d+1)\)-dimensional input space \(U\) containing \(t\). The map \(b\mapsto b(b+t)\) sends \(U\) onto a \(d\)-space \(V\). All \(t B(V,V)\) lie in \(\ker L\) by the Moore determinant identity, proving the bound. [Passage from flats to inputs](Green51BCHCompression.lean) · [Moore identity](Green51MoorePreimages.lean)

## Attaining the bound using a subfield

Let \(E\subsetneq K\) have binary dimension \(d\). A nonzero scalar \(s\) with \(sE\) in the image of \(u\mapsto u^2+u\) exists by rank-nullity. Indeed, the map sending \(s\) to the functional \(e\mapsto\operatorname{Tr}(se)\) has a \(d\)-dimensional target. The preimage of \(sE\) under \(u\mapsto u^2+u\) has dimension \(d+1\) and contains \(1\). Since \(B(sE,sE)\subseteq s^3E\), quotienting by \(s^3E\) gives a \(d\)-flat. Enlarging the kernel preserves the vanishing determinants on that input space, so all higher ranks work as well. [Scaled subfields](Green51BCHSubfieldFlats.lean) · [Extension to a prescribed kernel rank](Green51BCHDimensionBounds.lean)

Replay the closure from the pinned Formal Conjectures checkout with `lake env python3 /path/to/solved-conjectures/scripts/replay-research Green51BCHDimensionBounds`.
