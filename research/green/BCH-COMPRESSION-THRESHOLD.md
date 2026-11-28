# When a third discarded BCH coordinate forces an affine three-space

Let \(K=\mathbb F_{2^m}\), let \(H\) be a binary vector space, and let \(L:K\to H\) be binary linear. Write
\[
 A_L=\{(x,x^3,x^5,L(x^7)):x\in K\}.
\]
For every \(m\ge10\),
\[
 A_L+A_L\text{ contains an affine three-space}
 \quad\Longleftrightarrow\quad \dim_{\mathbb F_2}\ker L\ge3.
\]
The equivalence also holds when \(m\ge4\) and \(7\) is coprime to \(2^m-1\), including \(m=4,5,7,8\). Thus two is the exact maximum loss of binary dimensions in this coordinate over all these fields. The theorem measures the choice of linear projection in the BCH construction. An unrestricted bound on all Green 51 examples would require a different argument. [Exact threshold](Green51BCHThreshold.lean) · [Two-coordinate construction](COMPRESSED-BCH-BOUNDS.md)

## Constructing the flat

For a fixed nonzero difference \(t\), take input pairs \(x,x+t\) over a binary subspace \(U\) containing \(t\). Their projected fourth coordinate is affine on \(U\) if \(L\) kills every Moore determinant \(M(t,b,c)\) for \(b,c\in U\). The first three coordinates have kernel \(\{0,t\}\) after subtracting their value at zero. Consequently these pairs give a flat of dimension \(\dim U-1\) in the double. [Affine image of an input space](Green51BCHThreshold.lean)

Take three independent elements of \(\ker L\) and write them as \(u^2,v^2,w^2\). Put \(D=M(u,v,w)\ne0\) and \(B(x,y)=xy(x+y)\). The two identities
\[
 M(t,b,c)=t B(b(b+t),c(c+t)),\qquad
 B(B(x,y),B(x,z))=x^2 M(x,y,z)
\]
let us prescribe the three pair minors \(M(t,b,c),M(t,a,c),M(t,a,b)\) as \(u^2,v^2,w^2\). Their independence forces \(t,a,b,c\) to span four dimensions, and alternation and bilinearity show that \(L\) kills \(M(t,U,U)\) throughout this span. [Determinant realization](Green51MoorePreimages.lean)

The realization needs one nonzero \(s\) making all three values \(s^7D^2B(v,w)\), \(s^7D^2B(u,w)\), and \(s^7D^2B(u,v)\) lie in the image of \(z\mapsto z^2+z\). This image has binary codimension one. Its three membership tests on \(s^7\) form a binary cubic map to \(\mathbb F_2^3\). The Green 53 polynomial-fiber bound gives at most \(2^9\) translations of its zero fiber covering \(K\). Since zero belongs to that fiber, it contains another point whenever \(2^m>2^9\). If seventh powers permute \(K^\times\), rank-nullity finds a nonzero solution already at \(m\ge4\). Setting \(t=(s^3D)^{-1}\) then gives the prescribed determinants. [Simultaneous Artin–Schreier equations](Green51SeventhPowerFibre.lean) · [Binary polynomial fibers](Green53PolynomialColours.lean)

The initial odd-power coordinates are the classical BCH columns. The converse above uses their fourth coordinate together with the support bound for binary low-degree polynomials. [Bose and Ray-Chaudhuri](https://doi.org/10.1016/S0019-9958(60)90287-4) · [Pinned Green 51 statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

To replay the notebook dependencies and kernel-check the result, run `lake env python3 /path/to/solved-conjectures/scripts/replay-research Green51BCHThreshold` from the pinned formal-conjectures checkout.
