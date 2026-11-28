# Finite lower tails and moments across reduced prime classes

Put \(R(p)=S(p)/p-\tfrac12\log p\) for the original signed double sum. Assume ordinary Siegel–Walfisz. There are absolute \(\gamma,\eta>0\) such that for every \(\varepsilon>0\) there is a constant \(b\ge0\) with the following property. At every sufficiently large integer \(X\), put \(h=\log\log\log X-b\). Simultaneously for both signs \(z\in\{-1,1\}\), all \(q\le e^{\eta h}\), and every reduced \(r\bmod q\),
\[
 \#\{p\le X:\ p\text{ prime},\ p\equiv r\bmod q,\ zR(p)\ge h^2/(64\pi^2)\}
 \ \ge\ \gamma\,\pi(X)/(\log X)^\varepsilon .
\]
The denominator counts all primes. In particular, the class \(1\bmod8\) contains large fluctuations of both signs about the leading term. Pointwise positivity concerns the sign of \(S(p)\) itself. [Original-sum theorem](ThetaFiniteLowerTail.lean) · [Pinned signed sum](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean)

The underlying inequality allows every sufficiently large \(h\) with \(128\exp(48e^h)\le\log X\). In every reduced class modulo \(q\le e^{\eta h}\), at least \(\gamma\pi(X)\exp(-48e^h)\) primes satisfy the indicated signed height bound. Taking \(b=\log\max(96,48/\varepsilon)\) gives the displayed estimate. The [unconditional finite upper tail](MOVING-PRIME-DEVIATIONS.md) and this conditional lower tail have double-exponential order in the square root of the deviation height in their common range. The constants in the exponents differ. [Finite transfer](ThetaFiniteLowerTail.lean) · [Earlier limiting excursions](ALL-CLASS-EXCURSIONS.md)

There is an absolute \(c>0\) such that for every sufficiently large \(X\) and all sufficiently large positive integer orders \(k\), with the two thresholds chosen separately, simultaneously for both signs and every reduced class with \(\log q\le(\eta/8)\min(\log k,\log\log\log X)\),
\[
 \frac1{\pi(X)}\sum_{\substack{p\le X\\p\equiv r\bmod q}}
       \max\{0,zR(p)\}^k
 \ \ge\ \big[c\min\{\log k,\log\log\log X\}^2\big]^k.
\]
For \(k\le(\log\log X)^A\) with any fixed \(A>0\), this and the unconditional empirical upper bound give two-sided growth of order \((\log k)^2\) for the moment root, simultaneously in all reduced classes with \(q\le k^{\theta_A}\) for some \(\theta_A>0\). The lower constant and \(\theta_A\) may depend on \(A\). The formal lower estimate takes \(h=\min(\log k,\log\log\log X)/8\), uses \(48e^h\le e^{4h}\) for \(h\ge4\), and sums the \(k\)-th powers on the resulting exceptional primes. [One-sided empirical moments](ThetaFiniteLowerMoments.lean) · [Upper moments](ThetaEmpiricalPrimeMoments.lean)

## Uniform choice of the residue class

Take \(P=\lfloor 2\eta\log T\rfloor\). Lift the inverse of \(r\bmod q\) to a unit modulo \(q\prod_{p\le P}p\). This gives an odd representative \(a\) with \(\log a\le4P\), no prime factor at most \(P\), and
\[
  \sum_{p\mid a}\frac1p \le \frac{\log a}{P\log P}\le\frac4{\log P}.
\]
For each divisor \(d\mid m\) coprime to \(a\), choose the same lifted unit \(n\bmod m\) with \(na\equiv1\bmod d\). Up to \((d-1)/a\), its row has the same signs as the identity row. The remaining harmonic weight in the first period costs at most \(2(1+\log(2a))\). Every later numerator cutoff costs at most \(2\log(2a)+5\) from the identity lower bound. For the exceptional divisors \(d\) sharing a prime with \(a\), sum the logarithmic row envelope over the multiples of each such prime. Relative to the squared divisor mass this contribution tends uniformly to zero. A sufficiently small absolute \(\eta>0\) absorbs the cost on the coprime rows and leaves the finite model mean at least \((\log T)^2/64\). Reflection supplies the other sign. [Rough inverse lift](ThetaRoughInverseClasses.lean) · [Uniform representatives](ThetaRoughRepresentatives.lean) · [Harmonic row comparison](ThetaInverseResidueRows.lean) · [Exceptional-divisor bound](ThetaRoughDivisorBudget.lean) · [Uniform finite model](ThetaCompactModels.lean)

## Why the shorter modulus suffices

For \(p\le T\), write \(w=p^{\lfloor\log_p T\rfloor}\). Then \(p\le w\le T<wp\), so \(T^2\le w^4\le T^4\). If \(p\) divides \(d/\gcd(m,d)\), the whole factor \(w^4\mid m\) divides \(\gcd(m,d)\). For each \(p\), its saturated divisors therefore carry logarithmic weight at most \((L_m+4\log T\,M_m)/T^2\), where \(M_m=\sum_{g\mid m}1/g\) and \(L_m=\sum_{g\mid m}(1+\log g)/g\). Summing over at most \(T\) choices, and adding the previously bounded large-quotient tail, gives an omitted contribution \(o(M_m)\). Every integer through \(T\) divides \(m\), so its captured reciprocal mass is at least the \(T\)-th harmonic number. [Compact modulus and size](ThetaCompactModulus.lean) · [Saturated-divisor estimate](ThetaCompactOmitted.lean) · [Uniform error](ThetaCompactSequence.lean)

## A finite fraction on one refinement

Set \(m=\mathrm{lcm}(1,\ldots,T)^4\). For every sufficiently large \(T\), every \(q\le T^\eta\) and every reduced \(r\bmod q\), there is a reduced \(b\bmod m\) refining that class. At every \(N\ge N_0\) with \(m\le\log N\), at least \(\beta\pi(N^{64})/\varphi(m)\) primes \(N^{56}\le p\le N^{64}\) in that refinement satisfy \(zR(p)\ge(\log T)^2/(64\pi^2)\). The absolute \(\beta>0\) works for both signs. The refinement can depend on \(T\) and the sign. The threshold \(N_0\) is chosen before \(T\). To pass to \(X\), take \(N=\lfloor X^{1/64}\rfloor\). Chebyshev's inequalities give \(\pi(N^{64})\gg\pi(X)\), and \(T=\lceil e^h\rceil\) gives \(\log m\le4(\log4+4)T\le48e^h\) by Chebyshev's bound on \(\psi(T)\). [Refinement count](ThetaGrowingExcursionCounts.lean) · [Moving signed prime mean](ThetaGrowingPrimeExcursions.lean)

For a finite set of primes, let \(\delta\) bound the absolute discrepancy of each residue count from uniform reduced-class mass at all moduli \(md\), \(1\le d\le Y\). A selected denominator-\(d\) row sees at most \(d\) residues modulo \(md\). The total discrepancy between the selected model sum and its complete unit mean times the ambient mass is at most \(3ZY(1+\log Y)\delta\), where \(Z=\sum_{g\ge1}g^{-2}\). At \(Y=m^{256}\), the largest required modulus is \(m^{257}\). The factorial period of the complete model does not enter the prime-distribution hypothesis. The squared error of the signed residual against the truncated model over a prime subset \(E\) is at most \(C|E|+B N^{64}/(\log N\, Y^{1/128})\). Combining these estimates with the captured finite progression mean gives a large signed first moment. A global quantile at \(t=4\log m\) bounds the very large residuals. Cauchy–Schwarz and the global second moment show their total contribution is at most \(\pi(N^{64})/\varphi(m)\) eventually. The remaining primes carry the stated positive fraction. [Row discrepancy](ThetaRowProgressionDiscrepancy.lean) · [Squared approximation error](ThetaMovingPrimeModelError.lean) · [Finite model reflection](ThetaReflectedWindowMeans.lean) · [Signed finite mean transfer](ThetaMovingProgressionMean.lean)

## External input and scope

Lean takes \(\texttt{ThetaSiegelWalfiszBand.Ordinary}\) as a hypothesis. For every pair of nonnegative integers \(A,B\), it bounds the discrepancy \(|\pi(X;q,b)-\pi(X)/\varphi(q)|\) by \(X/(\log X)^B\) eventually, uniformly for \(1\le q\le(\log X)^A\) and reduced \(b\bmod q\). Koukoulopoulos, *The Distribution of Prime Numbers*, Theorem 12.1, gives the classical estimate centered at the logarithmic integral. Applying the same estimate with \(q=1\) replaces the center by \(\pi(X)\); the exponential error absorbs any fixed inverse logarithmic power and its implied constant. The band conversion, including removal of all primes below \(N^{56}\), is proved in Lean. The original pointwise positivity and superlinear lower conjectures remain open in this development. [Ordinary hypothesis and band proof](ThetaSiegelWalfiszBand.lean) · [Koukoulopoulos, Theorem 12.1](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf) · [Berndt et al., v3](https://arxiv.org/pdf/2501.03234v3#page=4) · [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA pointwise partial](https://github.com/lefttosolve2/open-math-agents/pull/31296) · [Left to Solve](https://lefttosolve.com/solved/step#step)

A concurrent finite certificate proves \(2p<S(p)\) for primes \(233<p<100000\). Its conclusion is a pointwise lower bound on that interval. [OMA finite certificate](https://github.com/lefttosolve2/open-math-agents/pull/34398)

## Independent verification

A clean Lean 4.33.1 build and independent kernel replay checked 125 notebook modules and the pinned DeepMind arithmetic-sum module at `f606af160664c5a10952e9a957b100a1cd45bbeb`. The 522 distinct axiom reports use only `propext`, `Classical.choice` and `Quot.sound`. The analytic prime-distribution assumption appears in the theorem statements.
