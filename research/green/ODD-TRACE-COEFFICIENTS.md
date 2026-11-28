# An exact trace test for odd-degree BCH projections

Let \(K=\mathbb F_{2^{2k+1}}\) with \(k\ge2\), and let \(T:K\to\mathbb F_2\) be the absolute field trace. For \(a\ne0\) and any \(b\in K\), set
\[
 A=\{(x,x^3,x^5,T(ax^7),T(abx^7)):x\in K\}.
\]
The largest affine dimension in \(A+A\) is either \(k\) or \(k+1\). To decide which, form the polynomial
\[
 P_b(X)=\prod_{j=0}^{k-1}\bigl(X-b^{2^{\,2j+1}}\bigr)
       =\sum_{i=0}^k u_i X^{k-i}.
\]
The larger dimension occurs exactly when some \(h\in K^\times\) satisfies \(T(a^2h^7u_i)=0\) for every \(0\le i\le k\). This includes \(b=0,1\). Trace duality expresses every two-coordinate projection with a nonzero first coordinate in this form. The Lean statement uses mathlib's \(\mathrm{Algebra.trace}\) and the pinned \(\mathrm{maxCosetDim}\). Green 51 asks for the guarantee over all sets at a given density and remains open. [Exact test](Green51OddTraceCriterion.lean) · [Trace duality](Green51GoldForms.lean) · [Pinned question](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

**A ratio in any proper subfield always gives \(k+1\), for every \(a\ne0\).** For example, over \(\mathbb F_{512}\) the eight ratios in \(\mathbb F_8\) all give five. The degree-nine example with largest dimension four therefore needs a ratio generating \(\mathbb F_{512}\). [Proper-subfield theorem](Green51OddTraceSubfields.lean) · [Degree-nine example](ODD-TWO-BIT-BCH-PENCILS.md)

## Why the coefficients decide the dimension

Write \([x,y]=x^2y+xy^2\). After rescaling the field coordinates, a \((k+1)\)-flat in \(A+A\) corresponds to a common isotropic \((k+1)\)-space of \(T([x,y])\) and \(T(b[x,y])\) inside the hyperplane \(T(a^2h^7x)=0\). The first form has radical \(\mathbb F_2\cdot1\), so each common space of this size equals its orthogonal for the first form. The polynomial coefficients satisfy \(u_0=1\), \(u_{i+1}^4+u_{i+1}=b^2u_i^4+bu_i\), and \(b^2u_k^4+bu_k=0\). Starting at \(1\), these identities force every \(u_i\) into the common space. [Rescaling and forced vectors](Green51OddTraceFlats.lean) · [Coefficient recurrence](Green51PencilCoefficients.lean)

For the converse, write \(D\) for the binary span of the \(u_i\). The recurrence shows that every vector orthogonal to \(D\) for the first form is also orthogonal to \(D\) for the second. Since \(D\) contains the first radical, there is room in any hyperplane containing \(D\) to extend \(D\) to a common \((k+1)\)-space. If \(b\) generates \(K\), evaluating successive Frobenius translates of the product proves the coefficients linearly independent. In that case \(D\) itself is the unique common \((k+1)\)-space for the normalized forms. [Hyperplane extension](Green51PencilHyperplanes.lean) · [Independence](Green51PencilWindows.lean)

If \(b\) belongs to a proper subfield \(E\), all the coefficients belong to \(E\). The index of \(E\) is odd and at least three. Isotropy in \(E\) gives \(3\dim D<2k+1\). The maps \(h\mapsto T(a^2h^7u_i)\) are binary cubics. Taking a basis of \(D\) leaves few enough cubic tests to guarantee a common nonzero zero. [Seventh powers in subspaces](Green51SeventhPowerFibre.lean)

Gow and Quinlan discuss common isotropic spaces for systems of alternating forms. Plût, Fouque and Macario-Rat use polynomial chains in their treatment of singular quadratic pencils in odd characteristic. The binary recurrence and the seventh-power condition above are proved directly for this BCH graph. [Gow and Quinlan](https://maths.ucd.ie/~rodgow/alternatingnew.pdf) · [Plût, Fouque and Macario-Rat](https://arxiv.org/abs/1406.3163)

Replay from the pinned Formal Conjectures checkout with `lake env python3 /path/to/solved-conjectures/scripts/replay-research Green51OddTraceSubfields`.
