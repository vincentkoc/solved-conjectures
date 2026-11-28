# Exceptional primes for the signed theta sum

Write \(R(p)=S(p)/p-\tfrac12\log p\) for the signed integer sum in the pinned DeepMind file, \(w(x)=1+\log\log x\), and \(L=\log X\). There is an absolute \(A>0\) such that, for every sufficiently large integer \(X\),
\[
 \#\{p\le X:\ p\text{ prime},\ |R(p)|\ge A w(p)^2\}
 \ \le\ \pi(X)\exp\!\left(-\frac{L}{2^{25}w(X)}\right).
\]
The same right-hand side bounds the number of primes with \(S(p)\le kp\), for every fixed natural \(k\) and all \(X\) sufficiently large in terms of \(k\). Taking \(k=0\) counts every failure of strict positivity. Both counts include the prime 2. The proof uses an elementary lower bound for \(\pi(X)\) and has no unproved analytic hypotheses. [Original signed statements](ThetaMultiscaleExceptions.lean) · [Endpoint transfer](ThetaMultiscaleEndpoint.lean) · [Pinned sum and conjectures](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean)

The earlier bound saved \(\exp(-a_\varepsilon L^{3/4})\) at residual threshold \(\varepsilon\log p\). Here \(L/w(X)\) eventually exceeds every fixed power \(L^\alpha\) with \(\alpha<1\), while \(w(p)^2=o(\log p)\). This gives a sharper exception estimate for pinned Conjectures 1.1 and 4.4. The bound on the number of exceptions still tends to infinity. Positivity at every odd prime and the eventual pointwise lower bound remain open. The original paper's v3 Conjecture 3.3 asks for eventual lower and upper growth at every prime, with the upper side treated in the notebook's Fourier estimate. [Earlier exception bound](STRONG-PRIME-TAIL.md) · [Paper, §3](https://arxiv.org/pdf/2501.03234v3#page=4) · [Fourier estimate](FOURIER.md)

## Finite quantiles and moments

For an absolute \(D>0\), every sufficiently large \(X\) satisfies the two bounds below simultaneously throughout the indicated ranges.
\[
 \begin{aligned}
 \#\{p\le X:\ p\text{ prime},\ |R(p)|\ge D(1+\log t)^2\}
   &\le \pi(X)e^{-t}
   &&\left(1\le t\le\frac{L}{2^{25}w(X)}\right),\\
 \sum_{p\le X,\ p\text{ prime}} |R(p)|^m
   &\le \pi(X)\,[D(1+\log m)^2]^m
   &&\left(1\le m\le\frac{L}{2^{27}w(X)^2},\ m\in\mathbb N\right).
 \end{aligned}
\]
For \(t^2\le L\) the earlier quantile estimate already has this form. For \(t^2>L\), every prime in the sample satisfies \(w(p)\le w(X)\le2(1+\log t)\). The new exception estimate then supplies the desired count. For large moment orders the pointwise Fourier bound gives \(|R(p)|\le M L^2\). On the exceptional set the exponential saving absorbs \((ML^2)^m\) throughout the displayed range. The earlier empirical moment theorem covers the small orders. [Quantiles](ThetaMultiscaleQuantiles.lean) · [Moments](ThetaMultiscaleMoments.lean) · [Previous finite estimates](MOVING-PRIME-DEVIATIONS.md)

## Why the denominator ranges matter

Let \(m\) be a modulus whose prime factors are at most \(U\). Weight its divisors by \(d^{s-1}\) with \(s\ge0\) and \(s\log U\le\log(3/2)\). For each prime \(p\mid m\), the weighted mean of \(v_p(d)\) is at most \(6/p\). Summing with weight \(\log p\) bounds the mean of \(\log d\) by \(12\log U\). Splitting at \(U^{32}\) bounds the total tilted mass by a constant times \(\log U\). In particular, for \(Q\ge1\) and \(\log U\ge1\),
\[
 \sum_{\substack{g\mid m\\g\ge Q}}\frac{1+\log g}{g}
 \ \ll\ (\log U)^2 Q^{-s}.
\]
The bound is uniform in the exponents of the prime factors of \(m\). [Tilted prime valuations](ThetaTiltedDivisors.lean) · [Weighted divisor tail](ThetaSmoothDivisorTails.lean)

For a denominator \(d>Q^2\), at least one of \(\gcd(d,m)\) and \(d/\gcd(d,m)\) is at least \(Q\). The first case uses the divisor tail above. The second uses the summable tail already available for the quotient. This bounds the absolute value of the conditional mean of the entire window supported on \(d>Q^2\) by \(O((\log U)^2Q^{-s})\), for \(s\le1/16\). The multiplicative-orbit identity gives the estimate for all integer inputs, including nonunits. [Conditional projection](ThetaHighWindowProjection.lean)

Take \(P=2^h\asymp\log N\) on \(N^{56}\le p\le N^{64}\). Separate an initial range from successive blocks whose logarithmic denominator scales \(q\) double. At a high block expose the prime powers up to \(U=2^{\lfloor q/(1024(h+1))\rfloor}\) and use moment order \(2\lfloor P/q\rfloor\). The projection estimate with \(s=1/(16\log U)\) costs at most one per high block. The initial range costs \(O((h+1)^2)\). Thus the total deterministic contribution is \(O((h+1)^2)\). At every block the centered moment supplies a count saving \(\exp[-P/(65536(h+1))]\). The incomplete-period term is at most \(2\exp(18P)\) and is absorbed on this prime band. [Exact row decomposition](ThetaRowDissection.lean) · [Projection budget](ThetaBandProjectionBudget.lean) · [Centered moments](ThetaBandExponentialBounds.lean) · [Combined over all blocks](ThetaMultiscaleRows.lean)

The original-sum approximation and the mean-square estimate bound the discarded denominators above \(2^{4P}\). A single prime band then covers all but at most \(N^{56}\) integers at each sufficiently large endpoint. The elementary prime-count lower bound absorbs the band-count factor and \(\log X\). The resulting saving has the explicit coefficient \(2^{-25}\). Finite small primes can be absorbed in the same initial interval, so the slope bound has no additive error term. [Transfer to the original sum](ThetaMultiscalePrimeBand.lean) · [Band calibration](ThetaPrimeBandCalibration.lean) · [Endpoint scales](ThetaEndpointScales.lean)

## Kernel replay

Independent Lean 4.33.1 replay checked 119 modules, including the 118 notebook sources and the pinned DeepMind source. All 502 distinct axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.

## Source comparison

The DeepMind issue gives exact row identities and a pointwise remainder criterion. OMA and Left to Solve include finite-range and conditional statements. Lägeler studies phases of individual Hardy sums, and Liu and Zhang average powers over numerators. The checked sources supplied no matching endpoint bound for the signed sum over all numerators at each prime denominator. The earlier notebook estimates are the direct comparison. This is an independently verified partial result on the pointwise questions. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA finite certificate](https://github.com/lefttosolve2/open-math-agents/pull/34398) · [Left to Solve](https://lefttosolve.com/p/Arxiv.2501.03234.conjecture_4_2.R1.H1) · [Lägeler](https://arxiv.org/abs/2207.04828) · [Liu and Zhang](https://ir.library.osaka-u.ac.jp/repo/ouka/all/10379/1658ojm.pdf)

Codex assisted with the derivation and formalization. [Notebook replay instructions](../../README.md)
