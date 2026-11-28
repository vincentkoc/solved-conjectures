# The exceptional scalar BCH double in dimension six

Let \(A_l=\{(x,x^3,x^5,l(x^7)):x\in K\}\), where \(K\) is a binary field of dimension \(m\) and \(l\) is any nonzero binary linear functional. In the field of 64 elements, **36 of the 63 choices of \(l\) give a largest affine flat of dimension four in \(A_l+A_l\). The other 27 give dimension three.** In every other field dimension, the maximum is \(\lfloor m/2\rfloor+1\). This also covers \(m=1,2,3\). [Exact dimension and counts](Green51GoldSix.lean) · [Other field dimensions](Green51GoldSmall.lean) · [General polar bound](SCALAR-BCH-PROFILES.md)

One of the 27 maps therefore supplies 64 labels in \(\mathbb F_2^{19}\) whose double contains no affine four-space. In the pinned Green 51 formulation this gives \(\operatorname{guaranteedMaxCosetDim}(19,\alpha)\le3\) at every \(\alpha\le64/2^{19}\). The general problem remains open. [Host specialization](Green51GoldSix.lean) · [Pinned statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

## Testing a scalar projection

Write \(l(z)=\operatorname{Tr}(cz)\), \(c\ne0\), and put \(v=c^9\). A four-flat exists exactly when
\[
v=1 \quad\text{or}\quad v^3+v+1=0.
\]
All calculations take place in \(K\). [Coefficient test](Green51GoldCoefficient.lean)

At shift \(t\ne0\), a nonzero element \(r\) of the polar radical satisfies \(ct^7r^3=1\). The radical is then \(r\mathbb F_4\). This line is contained in the absolute trace hyperplane exactly when \(r+r^4+r^{16}=0\). For \(u=r^3\) the condition becomes \(u^5+u+1=0\), and
\[
u^5+u+1=(u^2+u+1)(u^3+u^2+1).
\]
The seventh powers in \(K^\times\) form its subgroup of order nine. Eliminating \(t\) from these two equations gives the test in \(v\). [Relative trace argument](Green51GoldRelativeTrace.lean) · [Four-flat equivalence](Green51GoldSix.lean)

The passing coefficients are the roots of \((X^9-1)(X^{27}+X^9+1)\). Multiplication by \(X^{27}+X^{18}+1\) gives \(X^{63}-1\). All 63 nonzero field elements satisfy that product, so the two degree bounds force the respective root counts 36 and 27. The nondegenerate trace pairing transfers those counts to scalar projections. [Counting proof](Green51GoldCoefficient.lean)
