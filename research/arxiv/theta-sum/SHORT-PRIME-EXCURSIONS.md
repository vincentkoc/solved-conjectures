# Short-interval excursions and consecutive sign changes of the theta residual

Write \(R(p)=S(p)/p-\tfrac12\log p\) for the pinned signed integer sum. Fix \(7/12<\theta<1\). Given the complete Weil bound and short-interval prime number theorem specified below, there are \(\eta>0\) and \(b\ge0\) such that, at every sufficiently large \(X\), each reduced class \(r\bmod q\) with \(\log q\le\eta(\log\log\log X-b)\) contains at least
\[
                         \tfrac18 X^{1-\theta}
\]
distinct pairs of consecutive progression primes in \((X,2X]\) with \(R(p)R(p')<0\). For \(q=1\) they are consecutive primes. [Counting theorem](ThetaCrossingFrequency.lean) · [Adjacent crossings](ThetaConsecutiveCrossings.lean) · [Original sum](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean#L41-L95)

The short-interval theorem gives the **sizes and counts** of excursions. An absolute \(\eta>0\) works for the admitted cutoffs. For every \(\varepsilon>0\) one can choose \(b_\varepsilon\ge0\) so that, for every sufficiently large \(X\), simultaneously for \(X^\theta\le H\le X\), \(h=\log\log\log X-b_\varepsilon\), \(q\le e^{\eta h}\), reduced \(r\bmod q\), and \(z=\pm1\),
\[
 \#\{X<p\le X+H:\ p\ \mathrm{prime},\ p\equiv r\bmod q,\ zR(p)\ge h^2/(64\pi^2)\}
 \ \ge\ H/[2(\log X)^{1+\varepsilon}].
\]
Both signs refer to the error after the leading \(\tfrac12p\log p\) term. Pointwise positivity of \(S(p)\) remains open. Earlier short-interval results establish local first-order growth. The global lower-tail theorem counts excursions in cumulative prime samples. [Short-interval signed counts](ThetaShortExcursionTails.lean) · [Earlier first-order result](SHORT-PRIME-INTERVALS.md) · [Global lower tails](FINITE-LOWER-TAILS.md)

## Proof

Use an interval-specific band parameter \(N\) with \(N^{56}\le p\le N^{64}\) and let \(Y=\lfloor\log X\rfloor^{1024}\). Replacing the common-factor cutoff in the low rows costs at most three units of the finite row model. The translated high-row energy bounds the number of offsets where the signed model has more than a fixed absolute error by \(O((1+\log N)^8[H/Y^{1/64}+N^e])\). Here \(e=48\) for the elementary complete-sum bound and \(e=32\) under Weil. The estimate is valid at every translation in the specified band. [Signed model and exceptional count](ThetaLocalModelError.lean) · [Choice of cutoff](ThetaLocalExcursionScales.lean)

In a class of the compact modulus \(m=\operatorname{lcm}(1,\ldots,T)^4\) the conditional finite-model mean has the requested sign and size. Each row with index \(d\le Y\) can be counted using a modulus at most \(md\le(\log X)^{1025}\). Ordinary short-interval equidistribution bounds the total discrepancy. The exceptional offsets cost at most one expected class count after multiplication by the supremum \(U=3Z(1+\log Y)^2\). This uses \(N^e(\log X)^{16}\le H\), which holds eventually for \(\theta>e/64\). The surviving signed primes give at least \(H/(2\log X\,\varphi(m)U)\) count in the chosen refinement. Taking \(T\) near \(e^h\) absorbs both the modulus and \(U\) into \((\log X)^\varepsilon\). [Prime-counting input](ThetaLocalPrimeCounts.lean) · [Error budgets](ThetaLocalExcursionBudgets.lean) · [Finite deletion](ThetaLocalExcursionCount.lean) · [Progression refinement](ThetaLocalSignedExcursions.lean)

For a prime with \(R(p)=0\), \(p\log p=2S(p)>0\). If two such primes \(p,q\) exist then \(p^{pS(q)}=q^{qS(p)}\), hence \(p=q\) by unique factorization. Beyond the possible single zero, positive and negative residuals in an interval force a strictly sign-changing adjacent pair in that class. Partition \((X,2X]\) into full cells of length \(\lceil(2X)^\theta\rceil\). Each supplies a pair with a distinct left endpoint. The counting theorem includes the ceiling, integer quotient and factor \(1/8\). [Zero uniqueness and adjacency](ThetaConsecutiveCrossings.lean) · [Packing](ThetaCrossingFrequency.lean)

## Analytic inputs

Lean proves the implication from \(\texttt{ThetaLocalPrimeCounts.Ordinary}\ \theta\) for \(\theta>3/4\) using the notebook's elementary kernel. With the additional \(\texttt{ThetaWeilShortIntervals.Weil}\) estimate it proves the implication for \(\theta>1/2\). The ordinary hypothesis is the unweighted discrepancy at most \(H/(\log X)^B\) from \(\varphi(q)^{-1}\int_X^{X+H}dt/\log t\), uniformly for each fixed pair \(A,B\) and \(q\le(\log X)^A\). [Lean inputs](ThetaLocalPrimeCounts.lean) · [Complete-sum normalization](ThetaWeilShortIntervals.lean) · [Weil, *On some exponential sums*](https://doi.org/10.1073/pnas.34.5.204)

For \(\theta>7/12\), Thorner and Zaman give the log-weighted estimate at polylogarithmic moduli in Theorem 1.1, Remark 1.2 and the display on p. 3 following (1.6). To deduce the unweighted input, choose \(7/12<\theta'<\theta\). In partial summation from \(X\), bound initial prefix lengths \(u<X^{\theta'}\) trivially by \(O(X^{\theta'}\log X)\), negligible compared with \(H/(\log X)^B\). On longer prefixes apply the weighted estimate at \(x=X+u\le2X\) with an exponent strictly between \(7/12\) and \(\theta'\). This absorbs the polylogarithmic factors in the length condition. Partial summation of the main term gives the specified integral. The case \(q=1\) follows from \(q=2\), since every sufficiently late prime is odd. This use of the published theorems is external to the Lean replay. [Thorner and Zaman, pp. 2–3](https://arxiv.org/pdf/2108.10878#page=3)

The original paper asks for positivity of \(S(p)\) and pointwise lower growth. The DeepMind issue gives a pointwise remainder reduction. The OMA records cover finite and harmonic partials. The LTS feed lists the pinned reductions. Searches by the paper ID, declarations and signed aggregate did not identify a matching formal short-interval secondary excursion or adjacent-crossing count. [Berndt et al., revised conjectures](https://arxiv.org/pdf/2501.03234v3#page=4) · [DeepMind](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA](https://github.com/lefttosolve2/open-math-agents/pull/31296) · [LTS](https://lefttosolve.com/api/solved)

Earlier notebook results count runs of primes with the correct first-order growth and recurring pairs at fixed gaps. The count here requires a strict change in the sign of the centered residual between adjacent primes. A concurrent OMA certificate proves pointwise lower growth up to 100000. [First-order runs](https://github.com/vincentkoc/solved-conjectures/pull/338) · [Fixed-gap patterns](https://github.com/vincentkoc/solved-conjectures/pull/346) · [Finite certificate](https://github.com/lefttosolve2/open-math-agents/pull/34398)

## Independent replay

A clean Lean 4.33.1 build independently replayed the pinned canonical source and all 157 notebook modules. The 588 distinct axiom reports used only `propext`, `Classical.choice`, and `Quot.sound`. All 157 notebook source hashes matched the staged proof.
