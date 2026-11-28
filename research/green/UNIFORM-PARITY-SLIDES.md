# Which parity slides preserve full coverage?

Let \(T=2A\cup(1+2B)\) be a full two-basis of \(\mathbb Z/(2v)\), with \(v\to\infty\) and \(|T|/\sqrt{2v}\to\sqrt2\). Suppose either parity layer contains all but \(o(\sqrt v)\) points of a seed \(D\subseteq\mathbb Z/v\) of size \((1+o(1))\sqrt v\). Assume a fixed upper bound on the ordered sum counts of \(D\). Add \(2h\) to the odd elements of \(T\), leaving the even ones fixed, to obtain \(T_h\). Then
\[
 \sup_{h:\,2h\ne0}
 \left|\frac{|T_h+T_h|}{2v}-\frac78\right|\longrightarrow0.
\]
Eventually \(T_h+T_h=\mathbb Z/(2v)\) **if and only if** \(2h=0\) in \(\mathbb Z/v\). Thus there is one full slide for odd \(v\), and two for even \(v\). Extra points in the retained layer and all elements of the opposite parity may be chosen freely subject to initial coverage and total size. [Uniform limits for either layer and exact full-slide criterion](Green33UniformParitySlides.lean)

There is also an unconditional conclusion about dense cyclic Sidon sets. For a Sidon seed \(D\) of size \((1+o(1))\sqrt v\), the set \(U=D+D\) satisfies
\[
 \sup_{t\ne0}\left|\frac{|U\cap(t+U)|}{v}-\frac14\right|\longrightarrow0.
\]
The same conclusion holds whenever the nonzero difference counts of \(D\) have mean-square error \(o(1)\) from one. The shift may depend on the seed. [Finite bound and dense Sidon theorem](Green33UniformSlideProfile.lean)

## Comparing the two autocorrelations

For a finite abelian group of order \(n\), put \(k=|D|\), let \(r,d\) be the ordered sum and difference counts, and set \(V=\sum_{t\ne0}(d(t)-1)^2\). Compare \(r\) to \(2\,1_U\) and \(d\) to the model \(p(t)=1+(k-1)1_{\{0\}}(t)\). The second comparison has squared error \(V\). Counting unordered pairs, including the diagonal, gives
\[
 \sum_x(r(x)-2\,1_U(x))^2
 = V-k^2-2k-n+1+4|U|
 \le V+k^2+1-n .
\]
For a Sidon seed \(V=n-1-k(k-1)\) exactly. The earlier translate-variation theorem gives identical autocorrelations for \(r,d\) at every lag. At a nonzero lag the model autocorrelation is \(n+2(k-1)\). Applying Cauchy–Schwarz to each comparison proves the finite bound in \(\texttt{uniform_intersection}\). If \(V=o(n)\) and \(k/\sqrt n\to1\), its error is \(o(n)\) uniformly. The argument uses the ordinary sumset and counts diagonal ordered pairs once. [Translate-variation identity](Green33ShiftVariation.lean) · [Cilleruelo, finite-group Sidon incidence identities, §2](https://arxiv.org/abs/1003.3576)

For the application, full critical bases balance the two parity budgets. Omitting \(o(\sqrt v)\) seed points therefore also allows only \(o(\sqrt v)\) extra labels. A label deletion can remove at most \(k\) self-sums, and deleting a point of a support can remove at most two pairs at any fixed nonzero difference. These edit bounds pass quarter-density translate intersections to the actual layer. The bounded-representation retention theorem gives \(V=o(v)\); one may also assume this variance condition directly. Substitution into the parity-slide count gives uniform seven-eighths coverage. Swapping the two coordinate layers shifts the old even layer by \(-1\) and reverses \(h\). [Retained difference profile](Green33BaerDifferenceProfile.lean) · [Parity-slide count](Green33ParitySlideCoordinates.lean) · [Earlier typical-slide law](PARITY-SLIDE-COVERAGE.md)

## Scope and checks

The result restricts critical witnesses that retain a specified seed in one parity class. Green's question asks whether unrestricted critical witnesses exist. Earlier notebook results concern reflection axes of Sidon and Singer sets, or concentration over most relative slides of arbitrary full bases. Here the Sidon conclusion concerns translations \(t+U\), and the full-basis conclusion holds at every shift outside the kernel of doubling. [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Reflected Sidon layers](REFLECTED-SIDON-LAYERS.md) · [Perfect difference centers](PERFECT-DIFFERENCE-CENTERS.md)

The finite bound was tested on all 7,172 subsets with a specified nonzero lag in cyclic orders two through nine. All 246 Sidon subsets in these groups gave the exact variance. Left to Solve lists Green 33 as research open. A targeted Open Math Agents search also returned an Erdős 1191 result about thinning distinct-difference blocks. DeepMind's statement issue and PR and the solved index were checked. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33) · [Erdős 1191 block result](https://github.com/lefttosolve2/open-math-agents/pull/16435)
