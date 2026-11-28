# Uniform prime tails and growing empirical moments of the signed theta sum

Write \(R(p)=S(p)/p-\tfrac12\log p\) and let \(\pi(X)\) count primes through \(X\). There is an absolute \(C>0\) such that at **every sufficiently large \(X\), simultaneously for all real \(t\ge1\)**,
\[
 \#\{p\le X:\ p\text{ prime},\
 |R(p)|\ge C[(1+\log t)^2+t^4/(\log X)^2]\}\le \pi(X)e^{-t}.
\]
The proof uses the signed sum from the pinned DeepMind file and an elementary lower bound for \(\pi(X)\). The earlier double-exponential bound chose the prime endpoint after the height. Here the endpoint is uniform, with an explicit second term for the largest deviations. [Finite quantiles](ThetaPrimeQuantiles.lean) · [Earlier limiting tails and moments](DOUBLE-EXPONENTIAL-TAILS.md) · [Pinned signed sum and conjectures](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean)

For another absolute \(C>0\), every sufficiently large \(X\) simultaneously satisfies, for every integer \(m\ge1\),
\[
 \frac{1}{\pi(X)}\sum_{p\le X,\ p\ {\rm prime}} |R(p)|^m
 \le \left(C\left[(1+\log m)^2+\frac{m^4}{(\log X)^2}\right]\right)^m .
\]
The \(m\)-th root is \(O((1+\log m)^2)\) throughout \(m^2\le(\log X)(1+\log m)\). This extends the upper bound on each fixed limiting moment to finite samples of increasing order. The lower estimate for fixed limiting moments in the earlier theorem does not supply a uniform lower bound for these growing orders. [Original empirical moments](ThetaEmpiricalPrimeMoments.lean) · [Moment transfer for finite samples](ThetaFiniteTailMoments.lean) · [Earlier fixed-order result](ThetaSharpPrimeMoments.lean)

## Choosing the moment order

There are absolute \(A,D,H>0\) and an absolute starting endpoint such that the fraction with \(|R(p)|\ge Ah^2\) is at most \(D e^{-kh/128}\) whenever
\[
 h\ge H,\qquad 1\le k\le e^{h/8},\quad k\in\mathbb N,\qquad 128 k^2h\le\log X.
\]
After increasing \(H\), taking the integer part of the largest admissible \(k\) gives the bound
\[
 \exp\left[-\frac h{512}\min\left(e^{h/8},
                \sqrt{\frac{\log X}{128h}}\right)\right],\qquad 512h\le\log X .
\]
In particular the bound is \(\exp[-he^{h/8}/512]\) as soon as \(128h e^{h/4}\le\log X\) and \(h\ge H\). This finite double-exponential estimate uses no progression prime number theorem. [Endpoint count](ThetaMovingOriginalTail.lean) · [Optimized order and double-exponential range](ThetaUniformPrimeTails.lean)

To obtain the quantile, take \(h=H+8\log(512t)+2^{25}t^2/\log X\) when \(2^{25}t\le\log X\). The two terms in the minimum then both supply an exponent of at least \(t\). For the larger \(t\) the global Fourier bound puts every prime below the stated threshold, after enlarging \(C\). For the moment estimate, use levels \(t=16mj\). The quantile at \(16mj\) is at most \(j^4\) times the quantile at \(16m\); the cost of raising this factor to the \(m\)-th power is absorbed by \(e^{-16mj}\). [Pointwise bound and inversion](ThetaPrimeQuantiles.lean) · [Global Fourier estimate](FOURIER.md) · [Empirical moment proof](ThetaEmpiricalPrimeMoments.lean)

## Incorporating the prime sieve into the centered moments

On \(N^{56}\le p\le N^{64}\), take \(U=\lceil e^h\rceil\) as the smooth-prime cutoff and \(T=\lceil e^{kh}\rceil\) as the row-denominator cutoff. The conditional projection costs \(O(h^2)\) in the residual. The centered exponential moment holds on each multiplicative orbit. The squared Ramanujan sieve weight is nonnegative and constant on each such orbit. Multiplying by that weight therefore multiplies the complete exponential-moment bound by at most its mean, which is the inverse sieve normalizer and is \(O(1/\log N)\). [Orbit weighting](ThetaSievedOrbitMoments.lean) · [Sieve normalization and invariance](ThetaPrimeSieve.lean) · [Cutoff inequalities](ThetaMovingScales.lean)

In the finite interval expand the two sieve factors separately from the centered rows. The two sieve periods yield a fixed factor \(N^6\) in the endpoint error. Only the product of the row periods is raised to the moment order. At order \(2k\), the endpoint after division by the threshold is at most \(2N^6e^{8k^2h}\). The discarded rows have prime variance \(O(N^{64}/[(\log N)T^{1/128}])\). Thus both the retained and discarded rows gain the prime-density logarithm before passing to \(\pi(X)\). [Mixed periodic endpoint](ThetaMixedPowerEndpoint.lean) · [Sieved finite moments](ThetaSievedCenteredMoment.lean) · [Discarded-row prime variance](ThetaSievedConcentration.lean) · [Band estimate](ThetaUniformPrimeBand.lean)

There is also an individual-prime formulation. One absolute \(C>0\) works for every natural \(m\). For each such \(m\) and every sufficiently large \(X\), the prime fraction with
\[
 |S(p)-\tfrac12p\log p|\ge C(m+2)^2p(\log\log\log p)^2
\]
is at most \(\exp[-(\log\log X)^m]\). In the moment-order inequality take \(t=\log\log X,\ h=8(m+2)\log t,\ k=\lceil t^{m+1}\rceil\). The small primes are counted in the endpoint estimate. The remaining primes satisfy \(X\le p^2\), where the triple logarithm at \(X\) is eventually at most twice the one at \(p\). [Prime-dependent threshold](ThetaTripleLogTail.lean)

These counts permit infinitely many exceptions to pointwise positivity. The pinned lower-growth conjecture asks for an eventual inequality at every odd prime. Berndt, Bhat, Meyer, Xie and Zaharescu formulate the paper's corresponding lower growth assertion in v3, Conjecture 3.3. The active DeepMind reduction concerns a pointwise remainder. OMA has a finite linear bound for primes below 100000 and Left to Solve indexes reductions. [Original paper, §3](https://arxiv.org/pdf/2501.03234v3#page=4) · [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA finite lower bound](https://github.com/lefttosolve2/open-math-agents/pull/31296) · [Left to Solve](https://lefttosolve.com/solved/step#step)

## Verification

Lean 4.33.1 compiled the original DeepMind source from revision `f606af160664c5a10952e9a957b100a1cd45bbeb` and all 144 notebook modules needed by the new results and existing affected consumers. Independent kernel replay accepted each of the 145 modules. The 557 distinct axiom reports listed only `propext`, `Classical.choice` and `Quot.sound`, or were axiom-free. The focused notebook replay roots are `ThetaEmpiricalPrimeMoments`, `ThetaTripleLogTail`, `ThetaShortPrimeDiameters`, `ThetaCenteredOriginalTail` and `ThetaStrongOriginalTail`. [Notebook replay](../../README.md#replay)
