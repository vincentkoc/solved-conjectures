# Uniform prime Singer overlap and the exceptional triple label

Let \(p\) be prime, \(K/\mathbb F_p\) a cubic finite field, and \(D\) the projective labels of the kernel of a nonzero \(\mathbb F_p\)-linear functional on \(K\). Write \(v=p^2+p+1\). For every sequence \(p\to\infty\) and every sequence of axes \(t\), the following ordinary sumsets satisfy
\[
 \frac{|(D+D)\cap(t-D-D)|}{v}\longrightarrow\frac14,\qquad
 \frac{|R+R|}{2v}\longrightarrow\frac78,\qquad
 R=2D\cup(1+2t-2D)\subseteq\mathbb Z/(2v).
\]
The second identity uses overlap at \(1+2t\). Both limits are uniform in the functional and axis. The proof uses the elementary prime-field quartic character bound and has no rank-four character-sum hypothesis. [Cyclic labels and reflected set](Green33SingerAllCharacteristics.lean) · [Finite bounds and limits](Green33PrimeSingerCounts.lean)

Every full ordinary basis \(B\supseteq R\) eventually satisfies \(|B|/\sqrt{2v}>s\) for every \(s<(3+\sqrt3)/(2\sqrt2)\). This is a restriction on completions that retain both entire reflected layers. Green 33 permits arbitrary \(A\subseteq\mathbb Z/q\) and asks for infinitely many orders with full ordinary coverage and normalized size within each positive tolerance of \(\sqrt2\). That unrestricted question stays open. [Repair bound](Green33PrimeSingerCounts.lean) · [Pinned DeepMind statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

## The exceptional label

For \(p\ge400\), at most one center has more than \(p+80(\lfloor\sqrt p\rfloor+1)+10\) ordered triple representations from \(D\). The previous lower bound \(p-80(\lfloor\sqrt p\rfloor+1)-8\) holds at every center. Repeated summands are included in both counts. [All-center lower bound](PRIME-SINGER-TRIPLES.md) · [Upper bound off one label](Green33PrimeSingerCounts.lean)

Take the affine chart \([U(\theta-x)]\), with \(x\in\mathbb F_p\), and write \(m\) for the monic minimal cubic of \(\theta\). A center with representative \(W\) corresponds to the quadratic numerator \(u\) with \(u(\theta)=W/U^3\). The residual quadratic for the second parameter has discriminant \(\Delta_u(X)\). Over the cubic splitting field this polynomial is a square exactly when \(u\) is a base-field scalar times \(m'(X)^3\bmod m(X)\). The exceptional projective label in this chart is therefore \([U^3 m'(\theta)^3]\). [Pencil, residual quadratic and Stepanov bound](Green33SingerCubicFibers.lean) · [Square-pencil classification](Green33SingerExceptionalLabel.lean)

To see the classification, let \(r,s,t\) be the three distinct roots of \(m\). Write \(a=u(r)/m'(r)\), with \(b,c\) defined cyclically. A quadratic square root of \(\Delta_u\) is determined by its signs at the three poles. For a mixed sign choice its squared candidate differs from the discriminant by a nonzero product of linear factors. The common-sign choice gives two coefficient equations, equivalent to
\[
 a(s-t)^2=b(t-r)^2=c(r-s)^2 .
\]
Since \(m'(r)^2(s-t)^2\) is independent of the pole, the numerator values are proportional to the derivative cubes. Quadratic interpolation and comparison of one nonzero coefficient descend that proportionality to the base field. The argument also proves the converse by polynomial identity. Ferraguti and Micheli treat degree-three permutation rational functions via arithmetic and geometric monodromy and discriminants. Their permutation classification gives background for this square test. [Interpolation proof](Green33SingerExceptionalLabel.lean) · [Ferraguti and Micheli, §4](https://arxiv.org/abs/1805.03097)

## Counting and finite error

Every affine ordered triple for the specified label belongs to its residual fibre. Indeed, the product equation at \(\theta\) determines all three coefficients of the difference of two monic cubics. This argument also handles repeated roots. A triple containing the point at infinity costs at most six representations, since the two remaining labels form a Sidon pair in each of the three positions. The upper character bound controls every remaining label except the one square class. [Affine chart](Green33PrimeSingerTriples.lean) · [Projective count](Green33PrimeSingerCounts.lean)

Write \(I=|(D+D)\cap(t-D-D)|\) and \(A=|R+R|\). For \(p\ge400\),
\[
 |4I-v|\le(p+1)\bigl(80(\lfloor\sqrt p\rfloor+1)+16\bigr)+1,\qquad
 |4A-7v|\le(p+1)\bigl(80(\lfloor\sqrt p\rfloor+1)+24\bigr)+5 .
\]
Summing the triple count over the fourth point hits the exceptional center at most once. Its contribution is at most \(2(p+1)\) by the Sidon property. The remaining terms use the two-sided triple estimate. The four-step overlap and doubled-count identities account for the diagonal terms in the ordinary sumset. [Diagonal correction](Green33ReflectedLayers.lean) · [Doubled count](Green33PerfectDifferenceCenters.lean)

## Replay and prior work

Lean 4.33.1 rebuilt the 23-module dependency closure. Independent kernel replay passed for every module, including the final repair bound. All 147 axiom reports use only `propext`, `Classical.choice` and `Quot.sound`. A separate elaboration inspected the pinned declaration and proved that, along these prime orders, every full completion retaining the two layers eventually violates the literal size tolerance `1/100`. The notebook replay entry point accepts `Green33PrimeSingerCounts`. [Replay instructions](../README.md) · [Pinned declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

The earlier notebook proves the prime-field lower triple estimate and gives the all-characteristic limits assuming a rank-four estimate. The new upper estimate and prime-field limits remove that hypothesis. The DeepMind and Open Math Agents trackers returned no matching implementation in the targeted Singer triple and exceptional-label searches. The Left to Solve solved index had no entry for the parent. [Prior prime estimate](https://github.com/vincentkoc/solved-conjectures/pull/396) · [All-characteristic conditional result](Green33SingerAllCharacteristics.lean) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33)
