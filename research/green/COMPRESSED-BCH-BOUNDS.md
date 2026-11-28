# Two fewer coordinates in the binary BCH construction

For every \(n\ge6\) there is a set of \(2^{\lfloor(n+2)/4\rfloor}\) labels in \(\mathbb F_2^n\) whose double contains no affine three-space. This doubles the earlier four-coordinate construction's label count when \(n\equiv2,3\pmod4\). In particular, sixteen labels fit in fourteen binary dimensions. The pinned Green 51 affine guarantee is exactly two throughout
\[
 \frac{2}{2^n}<\alpha\le\frac{2^{\lfloor(n+2)/4\rfloor}}{2^n}.
\]
Every set admitted in this interval has at least three labels, and their three pair sums together with zero contain a plane. [Construction and density interval](Green51BCHPlateau.lean) · [Previous four-coordinate bound](Green51SparseBounds.lean) · [Pinned Green 51](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

Let \(K=\mathbb F_{2^m}\) and let \(L\) be any binary linear map on \(K\) with kernel dimension at most two. Take the columns
\[
 (x,x^3,x^5,L(x^7)),\qquad x\in K.
\]
The first three coordinates determine the unordered input pair for every nonzero sum. A zero sum in those coordinates forces equal input labels, so the fourth coordinate is zero as well. Projecting an affine flat in the double onto the first three coordinates therefore preserves its dimension. For a flat of dimension at least three, the projected flat lies over a fixed nonzero input difference \(t\). Its input pairs fill a translate of a space \(U\) with \(t\in U\) and \(\dim U\ge4\). [Three-coordinate inverse theorem](BCH-AFFINE-FLATS.md) · [Projection and input pairs](Green51BCHCompression.lean)

The fourth coordinate on this translate is \(L(x^7+(x+t)^7)\). Every second additive difference along \(b,c\in U\) must vanish. Thus the kernel of \(L\) contains every binary Moore determinant
\[
 M(t,b,c)=tbc(t+b)(t+c)(b+c)(t+b+c).
\]
Choose independent \(t,b,c,d\) in \(U\). The three values \(M(t,b,c), M(t,b,d), M(t,c,d)\) are independent. By alternation and bilinearity in the last two arguments, each of their seven nonempty sums is another \(M(t,u,v)\) for an independent triple. For example, the sum of all three is \(M(t,b+c,b+d)\). The displayed product proves that every such value is nonzero. This contradicts the two-dimensional kernel bound. [Moore determinant rank](Green51MooreRank.lean)

Quotienting the fourth coordinate by a two-dimensional subspace therefore accommodates all \(2^m\) labels in \(4m-2\) binary dimensions. Padding gives the displayed bound for arbitrary \(n\ge6\). The odd-power columns come from the classical binary BCH construction. [Bose and Ray-Chaudhuri](https://doi.org/10.1016/S0019-9958(60)90287-4)

To replay the proof, run `lake env python3 /path/to/solved-conjectures/scripts/replay-research Green51BCHPlateau` from the pinned formal-conjectures checkout.
