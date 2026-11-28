# Small horizontal reciprocal sums forced by a small theta value

For \(p\) an odd prime, \(N<p\) and a nonzero integer \(j\), write
\[
 U_p(N,j)=\sum_{d=1}^N
       \exp\!\left(-2\pi i\,\frac{j\,\overline p}{4d}\right),
\]
where the inverse in each term is taken modulo \(4d\). For every \(0<\delta\), every sufficiently large odd prime satisfying \(S(p)\le p\log p/100\) has a pair \((N,j)\) with
\[
 \exp(\sqrt{\log p}/512)\le N\le p^{3/4+\delta},\quad N<p,\quad
 0<|j|\le 2^{41}N(\log N)^2,\qquad
 |U_p(N,j)|>\frac{N}{2^{28}\log N\log\log N}.
\]
This implication has no external analytic hypothesis. For fixed \(N,j\), the sum depends only on \(p\) modulo \(4\,\mathrm{lcm}(1,\ldots,N)\). Uniform exclusion of these pairs at large odd primes would imply every pinned Conjecture 4.4 lower bound. The pointwise sign itself remains open. [Original sum and hypotheses](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean) · [Single witness](ThetaHorizontalWitness.lean) · [Growth implication](ThetaHorizontalBox.lean) · [Paper](https://doi.org/10.1007/s00025-025-02584-2)

## A sublinear phase table

Fix \(0<\alpha<1/3\) and put \(R=\lfloor\sqrt p\,\exp(-(\log p)^\alpha)\rfloor\). On the sparse grid of prefix lengths from the [reciprocal-sum reduction](RECIPROCAL-RESONANCE.md), keep only \(m\le R\) in its allowed range and \(1\le j\le R\). Write \(M=\lceil 2^{30}\log p\,\log\log p\rceil\). Subject to the Bourgain–Garaev and complete Weil estimates, every sufficiently large odd prime with \(S(p)\le p\log p/100\) has at least
\[
    b\,(\log p)^{1/3}/(\log\log p)^{8/3}
\]
distinct grid lengths \(m\) at which \(M|U_p(m,j)|>2m\) for some positive \(j\le R\). Successive selected lengths have ratio at least \(3/2\). If every comparison on this grid fails eventually, one obtains the pinned Conjecture 4.4 conclusion for every fixed natural multiplier. [Witnesses and pinned implication](ThetaHorizontalScan.lean)

For each \(j\), the update \(U_p(m+1,j)=U_p(m,j)+e_{4(m+1)}(-j\overline p)\) computes all its prefixes in one pass. Changing \(j\) to \(-j\) conjugates the sum, so only positive multipliers enter the table. The full \(R\)-by-\(R\) table contains exactly \(R^2\le p\exp(-2(\log p)^\alpha)=o(p)\) phase terms. The grid uses at most \(2^{35}(\log p)^2\log\log p\,R=o(\sqrt p)\) norm comparisons. These bounds count phase terms and threshold comparisons. The implication runs from a small theta value to the existence of crossings. [Exact phase count, conjugation and prefix recurrence](ThetaHorizontalTable.lean) · [Comparison count](ThetaHorizontalScan.lean)

The crossings survive fixed-precision tabulation. Scale each unit phase by \(2M\) and record any pair of integers within one unit of its real and imaginary coordinates. Each signed coordinate then has magnitude at most \(2M+1\). If \(A,B\) are the integer prefix sums in a tested column, compare \(A^2+B^2\) with \((2m)^2\). A guaranteed norm crossing gives the strict integer inequality \(A^2+B^2>(2m)^2\) for **every** admissible rounding. Coordinatewise floors give one valid table. The same family of prefix lengths and multipliers works under all these choices. [Uniform rounding, coefficient bounds and integer test](ThetaIntegerScan.lean)

All phase rows can share a table of \(Q=32M+1\) trigonometric sample pairs. For a residue \(0\le a<D=4d\), use the integer address \(\lfloor Qa/D\rfloor<Q\). Replacing \(2\pi a/D\) by \(2\pi\lfloor Qa/D\rfloor/Q\) changes each scaled coordinate by at most \(2/5\). At the shared sample points, coordinate error at most \(3/5\) therefore suffices. In particular, rounding a scaled sample approximation with error at most \(1/10\) to its nearest integer gives a valid table. Thus \(O(\log p\,\log\log p)\) sine–cosine pairs suffice for all \(R^2\) integer lookups. [Shared samples and transfer to the pinned statement](ThetaPhaseLookup.lean)

There is a stronger statement with classical analytic inputs. Fix \(0<\alpha<1/3\). With the Bourgain–Garaev initial-sum estimate, at least \(b(\log p)^{1/3}/(\log\log p)^{8/3}\) distinct lengths satisfy the same lower bound for \(U_p\), for some absolute \(b>0\). They can be selected with successive ratios at least two. Each pair also satisfies
\[
 \max(N,|j|)\le p^{3/4}\exp(-(\log p)^\alpha).
\]
With the complete Weil bound as well, the factor \(p^{3/4}\) can be replaced by \(\sqrt p\). The constants in the short-multiplier bound and the norm threshold are independent of both inputs. Lean states each analytic bound as a hypothesis. [Joint bound on length and numerator](ThetaHorizontalBox.lean) · [Precise hypotheses](RECIPROCAL-RESONANCE.md) · [Bourgain–Garaev, Theorem 16](https://arxiv.org/pdf/1211.4184#page=10) · [Weil](https://doi.org/10.1073/pnas.34.5.204)

## Restricting the Fourier multiplier

On a resonant dyadic block, put \(I=i+1\), \(J=2^i\), \(H=65536 I\), \(L=\lfloor p/H\rfloor\), and \(T=4H^2\). The sum of the smoothed half-interval kernel weights outside signed frequencies \(1\le |t|_p\le T\) is at most \(2p^2/T\). Using the trivial norm bound \(n\) there costs at most \(4pn/(TL)\) in parity discrepancy. Since \(n\le2J\), this is at most \(4J/(65536I)\), leaving enough of the block discrepancy to detect a large initial sum. [Kernel tail](ThetaShortFrequencies.lean) · [Truncated discrepancy](ThetaTruncatedHalf.lean) · [Quotient parity](ThetaShortParity.lean)

For the selected cotangent index \(k<2J\), the odd-prefix identity uses multipliers \(c=(2k+1)t/2\) and \(c/2\) in the prime field. Multiplication by four supplies a signed representative \(j\) of magnitude at most \(8JT\) in either case. Since \(J\le N\le4J\) and \(I\le4\log N\), this yields \(|j|\le2^{41}N(\log N)^2\). The finite level count and separated selection still apply to the restricted witnesses. [Frequency height](ThetaMultiplierHeight.lean) · [Finite level](ThetaLowMultiplierLevel.lean) · [Prime window](ThetaShortMultiplier.lean) · [Many lengths](ThetaManyShortMultipliers.lean)

## Exchanging the moduli

Writing \(e_q(x)=\exp(2\pi i x/q)\), Bézout's identity for \(p,D\) gives
\[
 e_p(j\overline D)=e_D(-j\overline p)\exp(2\pi i j/(Dp)).
\]
Taking \(D=4d\) and summing yields an absolute difference of at most \(\pi |j|H_N/(2p)\) between the prime-field sum at multiplier \(j/4\) and \(U_p(N,j)\). The short-multiplier bound makes this error at most half the required prime-field signal for all sufficiently large primes in the window. To fit both \(N\) and \(|j|\) inside the displayed bound, apply the separated result with \(\alpha<\beta<1/3\). The extra decay absorbs \(2^{41}(\log p)^2\). [Exact reciprocity, residue dependence and approximation](ThetaAdditiveReciprocity.lean) · [Transfer](ThetaHorizontalWitness.lean)

The remaining estimate concerns unusually large reciprocal sums with controlled integer numerators over varying denominators. Garaev and Shparlinski study lower bounds for short prime-field reciprocal sums. The active continued-fraction reduction addresses prefix overshoot, and the cyclic convolution reduction extracts triple counts from base digits. Codex assisted with derivation and formalization. [Garaev–Shparlinski](https://arxiv.org/abs/2304.07953) · [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [Continued fractions](https://github.com/lefttosolve2/open-math-agents/pull/21388) · [Digit extraction](https://github.com/lefttosolve2/open-math-agents/pull/28465) · [LTS](https://lefttosolve.com/api/solved)
