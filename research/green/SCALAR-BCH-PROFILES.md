# One binary coordinate and the largest flat in a BCH double

Let \(K=\mathbb F_{2^m}\) and let \(l:K\to\mathbb F_2\) be a nonzero linear functional. Consider the \(2^m\) points
\[
A_l=\{(x,x^3,x^5,l(x^7)):x\in K\}\subseteq\mathbb F_2^{3m+1}.
\]
For every \(m\ge4\) other than six, the largest affine subspace contained in \(A_l+A_l\) has dimension **exactly \(\lfloor m/2\rfloor+1\)** for every choice of \(l\). In dimension six its dimension is three or four, with the radical criterion below deciding between them. [Profile theorem](Green51BCHScalarProfile.lean) · [Dimension-six criterion](Green51GoldIsotropy.lean)

For any nonzero linear map \(L:K\to H\), a flat of dimension \(d\ge3\) in the corresponding double satisfies \(2d\le m+2\). Taking \(H=\mathbb F_2\) gives the host bound
\[
\operatorname{guaranteedMaxCosetDim}(3m+1,\alpha)\le \lfloor m/2\rfloor+1
\quad(m\ge2,\ \alpha\le 2^m/2^{3m+1}).
\]
For example, in 37 dimensions a set of 4,096 points has no eight-dimensional affine subspace in its double. Green 51 in general remains open. [Lean specialization](Green51BCHScalarProfile.lean) · [Pinned definition](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

## The polar form

A flat of dimension \(d\ge3\) gives a nonzero first coordinate \(t\) and a \(d\)-dimensional subspace \(D\) of the trace-zero hyperplane. For all \(x,y\in D\), the projection kills \(t^7xy(x+y)\). Composing a nonzero projection with a scalar test therefore makes \(D\) totally isotropic for some polar form \(B_c(x,y)=\operatorname{Tr}(cxy(x+y))\), \(c\ne0\). Its radical consists of the solutions of \(c^2x^4+cx=0\), at most four elements. The orthogonal dimension formula gives the upper bound. This is the polar form of the classical Gold function \(\operatorname{Tr}(cx^3)\). Coşgun gives the general radical-polynomial method in Section 2. [Normalized flat](Green51BCHFlatDimensions.lean) · [Polar rank proof](Green51GoldForms.lean) · [Coşgun, *Finite Fields and Their Applications* 50 (2018)](https://doi.org/10.1016/j.ffa.2017.11.005)

For the matching lower bound, write \(l(z)=\operatorname{Tr}(cz)\). Choose a scaled copy of \(\mathbb F_4\) in even dimension or \(\mathbb F_2\) in odd dimension. The seventh-power intersection theorem supplies a shift \(t\) for which this copy lies in both the trace hyperplane and the radical of \(B_{ct^7}\). A maximal isotropic subspace of the restricted form then lifts to an affine flat in the double. When \(m=6\), a four-flat exists exactly when some \(B_{ct^7}\), \(t\ne0\), has a two-dimensional radical contained in the trace hyperplane. [Seventh-power intersections](Green51BCHSmallFields.lean) · [Construction and criterion](Green51GoldIsotropy.lean)
