# A uniform logarithmic saving for the prime theta sum

Let \(S(p)\) be the signed integer sum of Berndt, Bhat, Meyer, Xie and Zaharescu as defined in the pinned problem. For all sufficiently large primes,
\[
 |S(p)|\ll p(\log p)^{3/2}(\log\log p)^4 .
\]
Consequently \(S(p)=o_\varepsilon(p(\log p)^{3/2+\varepsilon})\) for every fixed \(\varepsilon>0\). Taking \(\varepsilon=1/2\) gives a strict improvement over the earlier \(O(p\log^2p)\) bound. The estimate is pointwise and includes the primes \(1\bmod 8\). The sign remains open. [Pinned \(S(p)\) and conjectures](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean#L36-L95) · [Earlier upper bound](FOURIER.md)

## Analytic input and formal scope

The Lean theorem `ThetaBourgainGaraev.original_bound` takes exactly `InitialSumEstimate` as a hypothesis. This is the bound
\[
 \max_{c\ne0}\left|\sum_{d=1}^{N}e_p(c/d)\right|
 \le c_0\,N\frac{(\log p)(\log\log p)^3}{(\log N)\sqrt{\log N}}
 \qquad(2\le N<p)
\]
for some \(c_0\ge1\) and all sufficiently large primes. Here division is in the prime field. Bourgain and Garaev's Theorem 16 supplies this input in the stated range. Its proof is external to the Lean development. The finite transfer, its application to \(S\), and the little-\(o\) consequence are formalized. The latter is `ThetaBourgainGaraev.log_power_saving`. The original paper's v3 Conjecture 3.3 also asks for a lower bound; this estimate only sharpens the upper side. [Bourgain–Garaev, Theorem 16](https://arxiv.org/pdf/1211.4184#page=10) · [Lean statement and transfer](ThetaBourgainGaraev.lean) · [Original conjecture](https://arxiv.org/pdf/2501.03234v3#page=4)

## From ordinary reciprocals to parity

On a dyadic block \(2^i\le j<2^{i+1}\) the denominator is \(2j+1\). For an endpoint \(T\), the sum over the odd integers up to \(2T\) is the ordinary reciprocal sum up to \(2T\) minus the sum up to \(T\) with multiplier \(c/2\). Subtracting endpoints gives four initial sums. This step accounts for the starting point in every partial block. If the external bound has numerator \(K\), the resulting absolute sum is at most \(128 K\,2^i/(i+1)^{3/2}\). [Odd-prefix identity and estimate](ThetaReciprocalPrefixes.lean)

For \(v=2k+1\) write \(x=(v/2)/(2j+1)\) in the prime field. The least residue of \(2x\) is odd exactly when the least residue of \(x\) exceeds \(p/2\). The sample contains no zero, so negation interchanges the two halves. Smoothing each half by shifts \(0,\ldots,L-1\) bounds the absolute parity discrepancy of a sample of length \(n\) by
\[
        2nL/p+4\big(H_H+p/(HL)\big)E ,
\]
where \(E\) bounds all its nonzero exponential sums. To obtain the harmonic factor, split at frequency \(H\), bound the interval transform by \(p/(2h)\), and use the additional \(1/h\) decay of the smoothing interval above \(H\). [Interval transform](ThetaIntervalKernel.lean) · [Finite smoothing inequality](ThetaSmoothedHalf.lean) · [Canonical quotient signs](ThetaReciprocalParity.lean)

## Summing the cotangent triangle

The cotangent block is bounded by transposing the two denominator sums and using partial summation. A discrepancy bound \(2^i(A+B/(i+1)^{3/2})\) gives at most \(4p(At^2+2B\sqrt t)\) after summing the first \(t\) levels. Take \(t=\lfloor\log_2p\rfloor\), \(H=t\), \(L=\lfloor p/t\rfloor\). Then \(A=4/t\) and \(B=512(H_t+2)K\). The other terms in the comparison to the original sum cost \(O(p\log p)\). Substituting the published estimate for \(K\) yields the stated bound. [Weighted blocks](ThetaShortReciprocalBlocks.lean) · [Dyadic sum](ThetaDyadicDiscrepancy.lean) · [Finite original-sum inequality](ThetaShortSumTransfer.lean)

Related work of Garaev and Shparlinski gives examples of large short reciprocal sums. The uniform bound used here allows those examples. The live DeepMind reduction, OMA and LTS were checked for overlap. Codex assisted with derivation and formalization. [Garaev–Shparlinski](https://arxiv.org/abs/2304.07953) · [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA reduction](https://github.com/lefttosolve2/open-math-agents/pull/21155) · [LTS index](https://lefttosolve.com/api/solved)
