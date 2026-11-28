# Reciprocal sums forced by a small theta value

Write \(T_p(a,N)=\sum_{n=1}^N e_p(a n^{-1})\), where \(e_p(x)=\exp(2\pi i x/p)\), and put \(L(p)=\exp(\sqrt{\log p}/512)\). Call a length exceptional if some nonzero multiplier modulo \(p\) satisfies
\[
 |T_p(a,N)|>\frac{N}{2^{27}\log N\,\log\log N}.
\]
All results below concern odd primes with \(S(p)\le p\log p/100\), including the case \(S(p)\le0\). [Original paper](https://doi.org/10.1007/s00025-025-02584-2) · [Pinned sum and conjectures](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean)

**A sparse set of test lengths.** Put \(M=\lceil 2^{30}\log p\,\log\log p\rceil\). At dyadic level \(i\le\lfloor\log_2p\rfloor\), test the multiples \(j\max(1,\lfloor2^i/M\rfloor)\) with \(0\le j<4M\). Keep only the lengths in \([3L(p)/4,\,p^{3/4+\delta}]\) below \(p\). There are at most \(2^{35}(\log p)^2\log\log p\) test lengths for all sufficiently large \(p\). If \(S(p)\le p\log p/100\), one such length \(m\) has a nonzero \(a\bmod p\) satisfying \(M|T_p(a,m)|>4m\). The original multiplier survives rounding because changing a prefix by \(k\) terms changes its value by at most \(k\). Uniform cancellation on this explicit grid suffices for the exact pinned Conjecture 4.4. This criterion still quantifies over every nonzero multiplier. [Grid construction and rounding](ThetaReciprocalMesh.lean) · [Count, witness and pinned implication](ThetaMeshObstruction.lean)

**Single length.** For each fixed \(\delta>0\), every sufficiently large such prime has an exceptional length \(L(p)\le N\le p^{3/4+\delta}\), \(N<p\). This uses the elementary three-quarter-power estimate for complete Kloosterman sums proved in the notebook. Eventual absence of exceptional lengths on this window implies the exact pinned Conjecture 4.4 conclusion for every natural multiplier. With the complete Weil bound, some witness satisfies \(N<805306368\sqrt p(\log p)^2\log\log p\). [Single witness and growth](ThetaReciprocalResonance.lean) · [Completion](ThetaInitialCompletion.lean) · [Weil window](ThetaSquareRootWindow.lean)

**Separated lengths.** Assume the initial-sum estimate of Bourgain and Garaev used in the [short-sum transfer](SHORT-RECIPROCAL-BOUND.md). There is an absolute \(b>0\) such that, for each \(0<\alpha<1/3\), every sufficiently large such prime has at least
\[
 b\,\frac{(\log p)^{1/3}}{(\log\log p)^{8/3}}
\]
exceptional lengths between \(L(p)\) and \(p^{3/4}\exp(-(\log p)^\alpha)\). Successive lengths differ by a factor of at least two. Under the complete Weil bound the same count and spacing hold with upper endpoint \(\sqrt p\exp(-(\log p)^\alpha)\). The multiplier may vary with the length. [Separated witnesses and sparsity criterion](ThetaManyReciprocalSums.lean) · [Below the completion scale](ThetaSubcriticalResonance.lean)

The same argument gives a sharper range at both ends. Write \(w=(\log p)^{1/3}/(\log\log p)^{8/3}\). There is a constant \(b>0\) for which at least \(8bw\) exceptional lengths lie in
\[
    [L(p)e^{bw},\,B e^{-bw}],
\]
where \(B=p^{3/4}\) with the elementary bound, or \(B=\sqrt p\) with Weil. These lengths are separated by factors of two. Their rounded grid lengths are distinct, stay above \(3L(p)e^{bw}/4\) and below \(B e^{-bw}\), and retain successive ratios at least \(3/2\). Each satisfies the grid signal inequality above. The count and range use Bourgain–Garaev. [Two-sided trimming](ThetaInteriorResonance.lean) · [Separated grid witnesses](ThetaMeshObstruction.lean)

The Lean proof takes the published estimate \(|T_p(a,N)|\le cN\log p(\log\log p)^3/(\log N)^{3/2}\) for \(2\le N<p\) as a hypothesis. The square-root conclusion additionally takes \(\left|\sum_{x\ne0}e_p(tx+a/x)\right|\le2\sqrt p\) for each \(a\ne0\). To establish the pinned growth conjecture by this route, one still needs cancellation, or a bound on the number of separated exceptional lengths. [Bourgain–Garaev, Theorem 16](https://arxiv.org/pdf/1211.4184#page=10) · [Weil](https://doi.org/10.1073/pnas.34.5.204)

## From a signed triangle to separate lengths

Take \(t=\lfloor\log_2p\rfloor\) and \(s=\lfloor\sqrt t/128\rfloor\). The original theta inequality forces the lower cotangent triangle to have absolute value at least \(pt/256\). Its dyadic blocks \(B_i\) satisfy \(|B_i|\le8p(i+1)\). All levels \(i<s\) together cost at most \(pt/1024\). If the remaining levels all had \(|B_i|\le p/1024\), they could not account for the triangle. On a large level, partial summation gives an interval of quotient signs with large discrepancy. Smoothing its half-interval test to height \(65536(i+1)\) and using the exact odd-prefix identity produces an ordinary initial sum at \(2^i\le N\le4\cdot2^i\). The elementary complete-sum estimate limits the size of \(2^i\). [Dyadic blocks](ThetaResonantBlock.lean) · [Initial sum](ThetaResonantPrefix.lean) · [Constants](ThetaResonanceScales.lean)

Let \(K=c\log p(\log\log p)^3\). Smoothing at height \(t\) bounds each block by \(O(p(1+(H_t+2)K/\sqrt{i+1}))\). The preceding trivial bound then gives \(O(pA)\) for each block, with \(A\asymp((H_t+2)K)^{2/3}\). At least \(t/(2^{21}A)\) levels at or above \(s\) must exceed \(p/1024\). Keeping the most populous residue class of levels modulo three gives factor-two spacing. [Finite cap and count](ThetaResonantCount.lean) · [Selection](ThetaResonantLengths.lean)

If the complete sums have norm at most \(2B\), completion puts all these lengths below \(O(B(\log p)^2\log\log p)\). A factor-two separated set in a logarithmic interval of width \(w\) contains at most \(2w+1\) lengths. For fixed \(0<\alpha<1/3\), the interval above \(B\exp(-(\log p)^\alpha)\) holds a vanishing fraction of the forced family. Taking \(B=p^{3/4}\) or \(B=\sqrt p\) gives the stated bounds. [Packing](ThetaResonancePacking.lean) · [Complete-sum hypotheses](ThetaSubcriticalResonance.lean)

Garaev and Shparlinski prove order-\(N\) sums at fixed polylogarithmic lengths and smaller lower bounds at longer lengths. The continued-fraction reduction of the theta problem identifies uniform control of prefix overshoot as its remaining pointwise step. LTS has a separate finite certificate of positivity for every odd prime below 100,000. Codex assisted with derivation and formalization. [Garaev–Shparlinski](https://arxiv.org/abs/2304.07953) · [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA reduction](https://github.com/lefttosolve2/open-math-agents/pull/21388) · [Integral means](https://github.com/lefttosolve2/open-math-agents/pull/27960) · [Grid limit](https://github.com/lefttosolve2/open-math-agents/pull/28015) · [LTS finite certificate](https://github.com/lefttosolve2/open-math-agents/pull/21967)
