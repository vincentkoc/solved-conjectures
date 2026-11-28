# Mixed differences in a critical cyclic basis

Let \(T\) be an ordinary two-basis of \(\mathbb Z/n\) with \(|T|/\sqrt n\to\sqrt2\). Choose any disjoint \(E,B\subseteq T\). If one block has uniformly bounded ordered sum counts, then
\[
 |(E-B)\cap(B-E)|=o(n).
\]
The modulus, blocks and their sizes can vary. The finite inequality behind this conclusion holds in every abelian group. [Disjoint-block theorem](Green33OrientedDifferences.lean)

**A perfect difference set imposes a line-intersection law on the opposite parity.** Write \(T=2A\cup(1+2B)\) in \(\mathbb Z/(2v)\). Let \(D\subseteq\mathbb Z/v\) have \(q+1\) points and exactly one ordered representation of each nonzero difference. Then \(v=q^2+q+1\). If \(q\to\infty\), \(T\) is a critical full basis and \(|D\setminus A|=o(q)\), put \(r(x)=|(D-x)\cap B|\). Then
\[
 \frac1v\sum_{x:r(x)>0}(r(x)-2)^2\longrightarrow0.
\]
Thus all but \(o(v)\) translates meet \(B\) in zero or two points. The equality \(T+T=\mathbb Z/(2v)\) also forces all mixed sums \(A+B\) to be present. The difference condition concerns \(D-B\), whose support is at most \((1/2+o(1))v\). [Finite and normalized parity results](Green33ParityDifferences.lean)

**Retaining a matching Singer line and Baer subplane forces a lower coefficient of \(3/2\).** Take the Singer plane of order \(q=t^2\). Use its cyclic line \(D\) in even coordinates and any translated rational subplane \(L\) in the same Singer chart in odd coordinates. For every full basis \(T=2A\cup(1+2B)\) with \(|D\setminus A|,|L\setminus B|=o(\sqrt v)\), as \(v\to\infty\),
\[
 \liminf |T|/\sqrt{2v}\ \ge\ 3/2 .
\]
Extra points in either parity are arbitrary. The frame and translate can vary, in every characteristic and for every small-field product rank. The same-coordinate hypothesis fixes the relative sign of the two layers. Reflecting only the subplane changes the mixed difference condition. [Blocking and Baer declarations](Green33BlockingDifferenceBudget.lean)

## The finite obstruction

Write \(P(T)=\binom{|T|+1}{2}-|T+T|\), including diagonal pairs. If \(r_{E+E}(s)\le C\) for all \(s\), then
\[
 |(E-B)\cap(B-E)|\le 2C P(T).
\]
For \(x=e-b=b'-e'\), the unordered \(B\)-pair has sum \(e+e'\). One can discard *every* such \(B\)-pair while preserving \(T+T\): the representing \(E\)-pair is disjoint from the discarded collection. At most \(P(T)\) pairs are discarded. Each has at most two orderings and each sum has at most \(C\) ordered \(E\)-pairs. In \(\mathbb Z/5\), \(E=\{0\}, B=\{1,4\}\) and \(T=E\cup B\) give equality with \(C=P(T)=1\) and two opposite differences. [Finite bound and kernel-checked sharp example](Green33OrientedDifferences.lean)

For parity layers, the negative of the mixed difference \(2x-1\) has coordinate \(1-x\). For any reference seed \(D\) of sum cap \(C\), the two orientations therefore give
\[
 2|D-B|\le v+2C P(T)+2|D\setminus A|\,|B|.
\]
For perfect \(D\), its sum cap is two, and its difference identity gives \(\sum r=(q+1)|B|\) and \(\sum r^2=q|B|+|B|^2\). The displayed bound controls the support term in \(\sum_{r>0}(r-2)^2=\sum r^2-4\sum r+4|D-B|\). At critical size both parities have \(q+o(q)\) labels. This yields the line-intersection law. [Perfect difference identity](Green33PerfectDifferenceCenters.lean) · [Parity balance](Green33SingerBasisCurves.lean)

If \(D-L=\mathbb Z/v\), missing \(e\) points of \(L\) costs at most \(e|D|\) mixed differences. With \(d=|D\setminus A|\) this gives \(v\le4P(T)+2d|B|+2e|D|\) for \(C=2\). When \(T\) is full, \(d=o(\sqrt v)\) and \(e|D|=o(v)\), completing the square gives the \(3/2\) bound without any initial upper bound on \(|T|\). Every Baer subplane meets each line: the scalar translate of the line form maps its three-dimensional small-field vector space into a two-dimensional space and hence has nonzero kernel. The Lean proof places this point in the actual cyclic chart. [General deletion budget and limiting lower bound](Green33BlockingDifferenceBudget.lean)

## Scope and checks

The difference-set incidence identities and the blocking property of Baer subplanes are classical. Cofman treats projective Baer subplanes, and the earlier notebook gives the cubic Singer chart and the parity balance used here. The pinned Green 33 question asks for infinitely many unrestricted positive moduli and full bases. The disjoint-block condition applies to any selected critical witnesses. The \(3/2\) obstruction additionally assumes the doubled square-order moduli and the two retained layers. The existence of unrestricted critical witnesses remains open. [Cofman on Baer subplanes](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/BB91D0DC483458BAEE00AA81BB05FEFA/S0008414X00037287a.pdf/baer-subplanes-in-finite-projective-and-affine-planes.pdf) · [Singer charts](Green33BaerCyclicCertificate.lean) · [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

An exhaustive check of disjoint nonempty blocks in the cyclic groups of orders five through eight attained the finite coefficient two at every order. In the plane of order four, all 360 translated rational subplanes have full mixed *difference* support with the Singer line. Reflecting them gives support sizes 18 through 21 in the group of order 21. This small-plane calculation distinguishes the orientations and supplies no asymptotic estimate.

The live statement issue and statement PR, Left to Solve's problem and solved index, and targeted DeepMind, Open Math Agents and notebook searches were checked. Lean 4.33.1 rebuilt and independently replayed the 31-module import closure. All 190 printed declarations use only `propext`, `Classical.choice` and `Quot.sound`. A separate pinned-source replay derives the unrestricted orientation conclusion and rules out a selected critical sequence under the two-layer hypotheses. [Statement issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://www.lefttosolve.com/api/problems/Green33.green_33) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents) · [Replay instructions](../README.md#replay)
