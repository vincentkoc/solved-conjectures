# Three unordered sums in a square-order Baer layer

Let \(F=\mathbb F_t\), \(E=\mathbb F_{t^2}\) and \(K=\mathbb F_{t^6}\). Choose any \(E\)-linear frame \(K\simeq E^3\). The inverse image \(W\) of \(F^3\) gives a Baer subplane whose \(k=t^2+t+1\) points have cyclic labels \(B\subseteq K^\times/E^\times\simeq\mathbb Z/v\), where \(v=t^4+t^2+1\). Assume the \(F\)-span of the products of elements of \(W\) has dimension six.

**Every cyclic sum has at most three unordered representations in \(B\), with a repeated summand counted once.** The ordered count is at most six. This holds in every characteristic and every cyclic Singer chart, including after a cyclic automorphism. A translation shifts all sum labels by twice the translate. [Cyclic bounds](Green33BaerSidonCaps.lean) · [Projective factor bound](Green33BaerSidonFibers.lean)

**Almost-full retention forces a near-perfect difference profile.** Place \(B\) at \(z+2B\subseteq\mathbb Z/(2v)\). Suppose a full ordinary two-basis \(T\) has \(|T|/\sqrt{2v}\to\sqrt2\) and omits \(o(t^2)\) points of this layer as \(t\to\infty\). Then
\[
\frac1v\sum_{s\in\mathbb Z/v,\ s\ne0}
     \bigl(\#\{(a,b)\in B^2:a-b=s\}-1\bigr)^2\longrightarrow 0.
\]
In particular, all but \(o(v)\) nonzero base residues have exactly one ordered difference. The frame, coordinates and translate can vary with \(t\), and \(T\) can contain arbitrary other points. An unconditional positive lower bound for this normalized variance would exclude the corresponding family from almost-full retention. [Baer stability theorem](Green33BaerSidonCaps.lean)

## Counting the split products

Castello, Polverino and Zullo's Theorem III.2(4) identifies dimension six with the three-dimensional Sidon spaces over \(F\). In such a space, an equality of two nonzero products determines the two small-field factor lines up to order. The Lean lemma `rank_sidon` proves the direction used here. The cyclic labels identify products up to a scalar in the larger field \(E\), so one still has to count distinct small-field products on that \(E\)-line. [Classification](https://arxiv.org/pdf/2405.01652#page=2) · [Roth, Raviv and Tamo on Sidon spaces](https://arxiv.org/abs/1705.04560)

Distinct unordered representations of the same cyclic sum have disjoint factor labels. Start with a nondiagonal pair \(a,b\). For any second pair \(c,d\) at least one factor, say \(c\), lies outside the \(F\)-span of \(a,b\). Otherwise the \(E\)-linear independence of \(1,b/a,(b/a)^2\) would force a common factor label. In the basis \(a,b,c\) write \(d=ua+vb+wc\). The two small-field products span the whole \(E\)-line over \(F\). A third pair corresponds, up to scale, to a split ternary quadratic
\[
XY+rZ(uX+vY+wZ),\qquad r\in F^\times.
\]
The six independent basis products identify its coefficients. Vanishing of the ternary discriminant gives \(ruv=w\), including in characteristic two. If \(uv=0\), then \(w=0\) and \(d\) shares a factor label with the first pair. Thus a third pair determines the unique remaining parameter. Squaring is injective on the projective labels in this cubic extension, so a sum has at most one diagonal pair. [Pencil calculation](Green33BaerSidonPencil.lean) · [Adapted basis and counting](Green33BaerSidonFibers.lean)

## Finite variance bound

Let \(B\) be any \(k\)-element subset of a finite abelian group of order \(v\). Write \(V(B)\) for the sum of squared errors above and assume every ordered sum count is at most \(C\). For an injective additive embedding into a group of order \(n\), place any translate of the image inside that group. If a full basis \(T\) misses \(d\) points of the placed copy, then
\[
V(B)\le C\bigl(|T|^2+|T|-2n+d(2k+1-d)\bigr)+v-(k-1)^2.
\]
The sum and difference energies agree. At each supported sum, the ordered count plus the diagonal count is at least two. Summing gives \(V(B)\le C(k^2+k-2|B+B|)+v-(k-1)^2\). Each repeated unordered sum among retained points also spends an unordered pair of \(T\). This gives the displayed finite estimate, including its deletion term. For cyclic groups with \(v\to\infty\) and bounded \(n/v\), it implies \(V(B)=o(v)\) whenever \(k/\sqrt v\to1\), \(d=o(\sqrt v)\), \(C\) is fixed, and \(|T|/\sqrt n\to\sqrt2\). [Finite and normalized estimates](Green33BaerDifferenceProfile.lean)

## Scope and checks

Green 33 asks for critical full cyclic bases on infinitely many positive moduli. The result gives a necessary condition on selected witnesses along doubled square-order planes. The independent comparison takes the upstream full-sumset predicate and a vanishing absolute tolerance on the normalized size. The existence of such witnesses remains open. The complementary small-field collision class has a separate half-retention bound. [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Non-Sidon layers](NON-SIDON-BAER.md)

For \(t=2\), finite-field enumeration using \(x^6+x+1\) over \(\mathbb F_2\) found 168 distinct translated rank-six layers. Of these, 126 had maximum unordered count two and variance 30. The other 42 had maximum three and variance 38. The enumeration included every frame by normalizing one nonzero vector to 1 and ranging over the other two frame vectors. This gives sharpness for the unordered bound in the plane of order four.

Targeted DeepMind, Open Math Agents and personal-notebook searches covered the Sidon and Baer terms. The pinned statement issue and PR concern the problem statement. Left to Solve lists Green 33 as research open. [Statement issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents) · [Left to Solve](https://www.lefttosolve.com/api/problems/Green33.green_33)

Lean 4.33.1 rebuilt and independently kernel-replayed the 27-module import closure. Its 172 printed declarations use only `propext`, `Classical.choice` and `Quot.sound`. The separate pinned-witness application passed the same kernel and axiom checks. [Replay instructions](../README.md#replay)
