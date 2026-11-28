# Three discarded BCH coordinates over the field of order 64

Let \(K=\mathbb F_{64}\) and \(A_L=\{(x,x^3,x^5,L(x^7)):x\in K\}\), where \(L\) is binary linear. Some \(L\) with \(\dim\ker L=3\) has no affine three-space in \(A_L+A_L\). Every \(L\) with \(\dim\ker L\ge4\) gives an affine three-space. Thus three is the maximum number of dimensions one can discard from the seventh coordinate in this field. In every other field dimension \(m\ge4\) the maximum is two. [Three-dimensional kernel](Green51BCHSafeThree.lean) · [Four-dimensional obstruction](Green51BCHFourForces.lean) · [Other field dimensions](SEVENTH-POWER-ORBIT.md)

The quotient construction gives 64 points in \(\mathbb F_2^{21}\). Its double contains no affine three-space. With the two-dimensional lower bound for sets of more than two points, this gives
\[
 \operatorname{guaranteedMaxCosetDim}(21,\alpha)=2
 \qquad\text{for}\qquad \frac{2}{2^{21}}<\alpha\le\frac{64}{2^{21}}.
\]
The preceding construction gives 32 points in the same dimension. The general Green 51 question remains open. [Lean statement and host specialization](Green51BCHExceptional.lean) · [Previous bound](COMPRESSED-BCH-BOUNDS.md) · [Pinned Green 51 problem](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

## Why a three-dimensional kernel can avoid a flat

A flat in the double supplies a nonzero difference \(t\) and a four-dimensional input space \(U\) containing \(t\). Its Moore determinants \(M(t,b,c)\) lie in the kernel. Put \(N_t(x)=(x/t)^2+x/t\) and \(B(u,v)=uv(u+v)\). Then \(M(t,b,c)=t^7 B(N_t(b),N_t(c))\), and \(N_t(U)\) is a three-dimensional subspace of the five-dimensional image \(E\) of \(x\mapsto x^2+x\). The pair determinants on \(U\) span at least three dimensions. A three-dimensional kernel containing them must therefore equal their span. [Candidate kernels](Green51BCHCandidates.lean)

There are at most nine possible scalars \(t^7\) and 155 three-spaces in \(E\), giving at most \(9\cdot155=1395\) candidates. The field itself has exactly 1395 three-spaces. One repeated candidate suffices. Take \(\omega\) of order three and choose a three-space \(D\) inside \(E\cap\omega^{-1}E\), whose dimension is at least four. The spaces \(D\) and \(\omega D\) are distinct. If they agreed, multiplying their seven nonzero elements would give \(\omega^7=1\). Yet \(B(\omega u,\omega v)=B(u,v)\), so both spaces give the same candidate. Some kernel is missed. [Plane counts](Green51BinaryThreePlanes.lean) · [Repeated candidate](Green51BCHCandidateCollision.lean)

## Why four discarded dimensions force a flat

Fix \(t=1\). A projection with kernel dimension at least four has at most two independent output coordinates. On a five-dimensional complement of the direction \(1\), those coordinates of \(M(1,b,c)\) give two alternating forms. Over any field, two alternating forms in dimension \(2k+1\) have a common totally isotropic \((k+1)\)-space. The Lean proof takes a vector in the radical of the first form, restricts to a complementary space orthogonal to that vector for the second form, and inducts. In dimension five this gives a three-space. Adjoining the direction \(1\) gives a four-space of inputs whose pairs form an affine three-space in the double. [Simultaneous isotropy lemma](Green51TwoAlternating.lean) · [Application](Green51BCHFourForces.lean)

The odd-power columns are the classical BCH construction. Gow and Quinlan discuss the general common-isotropy question for families of alternating forms. The finite-field counting and isotropy arguments above are both checked in Lean. [Bose and Ray-Chaudhuri](https://doi.org/10.1016/S0019-9958(60)90287-4) · [Gow and Quinlan, §1](https://maths.ucd.ie/~rodgow/alternatingnew.pdf)

Replay the theorem and its notebook dependencies from the pinned Formal Conjectures checkout with `lake env python3 /path/to/solved-conjectures/scripts/replay-research Green51BCHExceptional`.
