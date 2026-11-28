# Non-Sidon Baer subplanes in a doubled cyclic plane

Put \(F=\mathbb F_t\), \(E=\mathbb F_{t^2}\), \(K=\mathbb F_{t^6}\), and \(n=2(t^4+t^2+1)\). Take any \(E\)-linear coordinate frame \(K\simeq E^3\) and let \(W\) be the inverse image of \(F^3\). Its nonzero vectors give a Baer subplane in \(K^\times/E^\times\). Write the quotient in additive cyclic coordinates, double the labels modulo \(n\), and translate by any residue. Call the resulting \(t^2+t+1\) labels \(B\).

The hypothesis on \(W\) is a multiplicative collision over the **small field**. There are nonzero \(a,b,c,d\in W\) with \(ab=cd\) and \(a\notin Fc\cup Fd\). For every such layer, as \(t\to\infty\), the following hold.

- Every full cyclic two-basis \(T\) with \(|T|/\sqrt n\to\sqrt2\) satisfies \(\limsup |T\cap B|/t^2\le1/2\). The frame, cyclic coordinates and layer translate can all vary. The points of \(T\) outside the layer are arbitrary.
- Every full cyclic two-basis \(T\) retaining all but \(o(t^2)\) points of \(B\) satisfies \(\liminf |T|/\sqrt n\ge 5/\sqrt{12}\). The Lean statements express both bounds by eventual strict comparisons with every coefficient on the appropriate side. [Cyclic declarations](Green33BaerCyclicCertificate.lean)

Castello, Polverino and Zullo classify three-dimensional small-field spaces by the dimension of the span of their products. In particular their Theorem III.2(4) identifies the Sidon case with square-span dimension six. The Lean hypotheses use an explicit collision. They include the polynomial model \(W=\langle1,s,s^2\rangle_F\) for \(s\) of degree six over \(F\), where \(1\cdot s^2=s\cdot s\). The three displayed powers form an \(E\)-basis of \(K\). This model has square-span dimension five. The earlier notebook result controls multiplicative subfield cosets and their unions. [Classification, Theorem III.2](https://arxiv.org/pdf/2405.01652#page=2) · [Sidon space definition](https://arxiv.org/abs/1705.04560) · [Earlier Baer-layer obstruction](https://github.com/vincentkoc/solved-conjectures/pull/416)

## The forced subset

Set \(s=a/c=d/b\). Both \(c,b\) and their multiples by \(s\) lie in \(W\). The two elements \(c,b\) are independent over \(F\), as dependence would identify the lines of \(a,d\). Thus \(U=W\cap s^{-1}W\) and \(sU\) have dimension at least two inside the three-dimensional space \(W\). Their intersection gives \(y\ne0\) with \(y,sy,s^2y\in W\). The ratio \(s\) lies outside \(F\). Two nonzero vectors of \(W\) proportional over \(E\) are already proportional over \(F\), so \(s\notin E\).

The labels of \(s+i\), \(i\in F\), form a set \(X\) of size \(t\). Every \(y(s+i)(s+j)\) belongs to \(W\). If two products of the monic linear factors are proportional over \(E\) at \(s\), their polynomials agree up to this same scalar. Indeed \(s\) has degree three over \(E\), and the difference has degree at most two. Their leading coefficients force the scalar to be one, and their roots determine the unordered pair, including repeated factors. Consequently \(B\) contains a translate \(Q\) of \(X+X\) of size \(\binom{t+1}{2}\). Each projective point of \(W\) has \(t-1\) nonzero rational representatives, giving the exact size of \(B\). [Progression and projective pair count](Green33BaerSubline.lean)

## Counting and normalization

In a critical basis the two \(t\)-element factors of \(Q\) have product size \(t^2=O(|T|)\), so the sumset-factor theorem gives \(|T\cap Q|=o(|T|)=o(t^2)\). The remaining \(t^2+t+1-\binom{t+1}{2}\) points give the half-layer estimate. [Sumset-factor theorem](SUMSET-FACTORS.md)

For the second bound put \(H=T\cap Q\), \(h=|H|\) and \(k=|T|\). Every doubled label of \(H+H\) comes from a multiset of four roots, so it takes at most \(\binom{t+3}{4}\) values. Every repeated unordered-pair representation within \(H\) also spends one of the available pairs of \(T\). The full covering condition therefore gives
\[
n+\binom{h+1}{2}\le \binom{k+1}{2}+\binom{t+3}{4}.
\]
For \(|B\setminus T|=o(t^2)\), one has \(h/t^2\to1/2\) and \(n/t^4\to2\). Dividing the finite inequality by \(n\) yields the squared coefficient \(2+1/8-1/24=25/12\). [Finite and limiting counts](Green33BaerQuadraticRetention.lean)

## Relation to Green 33

The pinned conjecture permits every positive cyclic modulus and asks for a full ordinary two-basis within each positive absolute tolerance of \(\sqrt2\) infinitely often. Here the modulus comes from a square-order plane and the conclusions bound occupancy of the specified layer. The existence of unrestricted critical bases and the case of a Sidon \(W\) remain open in this argument. The parameter family is unconditional and uses neither a character-sum estimate nor a special-characteristic assumption. [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

A separate finite-field enumeration used the primitive polynomial \(x^6+x+1\) over \(\mathbb F_2\). It exhausted the 120 rational vector spaces in a frame normalized to contain the vector 1 and their 360 distinct projective layers under Singer translations. Of these, 192 had a small-field collision. The translated three-element quadratic subset occurred in every one of the 192. Their self-sumsets had size 7, 16 or 18. The other 168 layers had self-sumset size 19 or 20. These counts concern the single plane of order four.

The Green 33 statement issue, statement PR, Left to Solve record and solved index, and targeted DeepMind, Open Math Agents and notebook searches were checked for this obstruction. [Statement issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://www.lefttosolve.com/api/problems/Green33.green_33) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents)

Lean 4.33.1 rebuilt the 23-module closure from source and replayed each module with the independent kernel checker. All 160 printed declarations use only `propext`, `Classical.choice` and `Quot.sound`. A separate kernel replay derived the half-layer inequality from the pinned positive modulus, full sumset and vanishing absolute tolerance. [Notebook replay](../README.md#replay)
