# An exact trace test for BCH graphs in even degree

Let \(K=\mathbb F_{2^m}\), where \(m=2k\ge4\), and write \(m=2^s t\) with \(t=2l+1\) odd. Write \(T\) for the absolute field trace. For \(a\ne0\) and \(b\in K\), consider
\[
 A=\{(x,x^3,x^5,T(ax^7),T(abx^7)):x\in K\}.
\]
The largest affine dimension in \(A+A\) is either \(k\) or \(k+1\). For the larger value, the ratio \(b\) must belong to \(\mathbb F_{2^t}\). Within that subfield, form
\[
 \prod_{j=0}^{l-1}(X-b^{2^{2j+1}})=\sum_{i=0}^l u_i X^{l-i}.
\]
The dimension is \(k+1\) exactly when there is an \(h\in K^\times\) with \(T(a^2h^7w u_i)=0\) for every \(w\in\mathbb F_4\) and every \(0\le i\le l\). This includes \(b=0,1\). The polynomial for \(t=1\) is the constant \(1\). Trace duality gives this parametrization for every pair whose first coordinate is nonzero. Green 51 asks about all sets at a prescribed density and remains open. [Lean criterion](Green51EvenTraceCriterion.lean) · [Pinned question](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

**If \(3\nmid m\), membership in \(\mathbb F_{2^t}\) alone decides the dimension.** Seventh powering permutes \(K^\times\), so any nonzero trace functional annihilating the forced coefficient space can be used. In degree ten, for instance, the 30 ratios in \(\mathbb F_{32}\setminus\mathbb F_2\) give dimension six for all 1,023 nonzero scales. The other independent ratios give five. In every power-of-two degree \(m\ge4\), every surjective two-coordinate projection gives dimension exactly \(m/2\). In degree six the full test recovers the 54 ordered independent maps with a four-flat. [Field criterion](Green51EvenTraceCriterion.lean) · [Power-of-two degrees](Green51EvenTraceRank.lean) · [Exact degree-six count](SIX-DIMENSIONAL-BCH-PENCILS.md)

## Why the odd subfield appears

The polar bracket is \([x,y]=x^2y+xy^2\). Write each field element in its full vector of Frobenius conjugates, pairing the even and odd exponents. Trace duality shows that independent binary vectors stay independent over \(K\) in these coordinates. In a linear combination of the forms for \(a\) and \(ab\), the weight on the first even edge vanishes. If every odd conjugate of \(b\) differs from \(b\), every odd edge has nonzero weight. The resulting cyclic matrix has trivial kernel by propagation around the cycle. Its nondegenerate form bounds a common isotropic space by \(m/2\). Any flat exceeding this bound consequently forces the entire dual coefficient space into one scalar multiple of \(\mathbb F_{2^t}\), even for projections with more than two coordinates. In particular their rank is at most \(t\). [Frobenius coordinates](Green51TraceMoore.lean) · [Cyclic form](Green51CyclicForm.lean) · [Rank bound](Green51EvenTraceRank.lean)

For a ratio in the odd subfield, the coefficient recurrence starts at \(1\) and ends in the radical of the second form. The first normalized radical is \(\mathbb F_4\), of binary dimension two. Multiplying the recurrence by each of its elements shows that \(D=\operatorname{span}_{\mathbb F_2}\{w u_i\}\) lies in every maximal common isotropic space. The same recurrence proves that \(D\) is common isotropic and that its first orthogonal annihilates the second form on \(D\). A dimension argument then extends \(D\) to a common \((k+1)\)-space inside any hyperplane containing it. Rescaling that hyperplane gives the seventh-power test. [Chain argument](Green51PencilChains.lean) · [Even-degree spaces](Green51EvenTraceSpace.lean) · [Common scaling](Green51TraceScaling.lean)

Gow and Quinlan study trace models of alternating forms from cyclic extensions. Plût, Fouque and Macario-Rat treat polynomial chains for quadratic pencils in odd characteristic. The two trace forms here arise from the polar form of a binary Gold monomial. The odd-degree companion test uses the same coefficients with a one-dimensional first radical. [Gow and Quinlan](https://arxiv.org/abs/0709.0741) · [Plût, Fouque and Macario-Rat](https://arxiv.org/abs/1406.3163) · [Odd-degree theorem](ODD-TRACE-COEFFICIENTS.md)

Replay from a pinned Formal Conjectures checkout with `lake env python3 /path/to/solved-conjectures/scripts/replay-research Green51EvenTraceCriterion Green51OddTraceSubfields`.
