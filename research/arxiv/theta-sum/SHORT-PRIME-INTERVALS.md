# Theta-positive primes in short intervals and residue classes

## Reduced residue classes at length \(x^{0.52}\)

For each fixed integer \(K\ge0\), \(c<1/2\), and \(\gamma<1/250\), every sufficiently large integer \(x\) satisfies the following bound simultaneously for \(1\le q\le(\log x)^K\) and all \((a,q)=1\):
\[
 \#\{x-x^{13/25}<p\le x:\ p\ {\rm prime},\ p\equiv a\pmod q,\ S(p)>cp\log p\}
 \ \ge\ \frac{\gamma x^{13/25}}{\varphi(q)\log x}.
\]
In particular this covers the open pointwise sign class \(p\equiv1\bmod8\) in every sufficiently late interval of this length. For each fixed \(\varepsilon>0\), the proportion in any such class violating \(\lvert S(p)-p\log p/2\rvert<\varepsilon p\log p\) tends to zero uniformly in \(q,a\). [Positive-prime count and uniform relative exceptions](ThetaShortProgressions.lean)

The two inputs are the complete Weil estimate and the ordinary progression lower bound in Runbo Li’s arXiv v8, Theorem 3. The latter supplies \(1/250\) at the backward endpoint \(x\); Lean takes its precise count as the hypothesis `Ordinary K`. The backward interval has integer left endpoint \(\lfloor x-x^{13/25}\rfloor\). The global count of exceptions in it is \(o_{\varepsilon,k}(x^{13/25}/(\log x)^k)\) for every fixed \(k\), using only Weil. This saves enough logarithms to compare against every progression denominator at once. [Endpoint equivalence](ThetaBackwardInterval.lean) · [Li, Theorem 3](https://arxiv.org/pdf/2308.04458v8#page=35) · [Weil’s original estimate](https://doi.org/10.1073/pnas.34.5.204)

For fixed $\varepsilon>0$, the run length in each reduced class grows as a stretched exponential. Put $y=\lfloor x-x^{13/25}\rfloor$. There is $a_\varepsilon>0$, independent of $K$, such that for $F=\exp(a_\varepsilon(\log y)^{3/4})$ and $P$ primes in the chosen class, at least $(1-3/F)P$ start a run of $\lfloor F\rfloor$ successive class primes all satisfying $|S(p)-\tfrac12 p\log p|<\varepsilon p\log p$. Every member of the run lies inside the window. For every $\rho>0$, at least $(1-\rho-3/F)P$ starts also have distance from first to last prime at most $500F\varphi(q)\log x/\rho$. Taking $q=1$ gives ordinary consecutive primes. These estimates use the two inputs stated above. [Run length and uniform quantifiers](ThetaCenteredPrimeRuns.lean) · [Diameter bound](ThetaShortPrimeDiameters.lean)

There is also a theorem for the full list of ordinary primes through $X$ without either short-interval input. With $F=\exp(a_\varepsilon(\log X)^{3/4})$, at least $(1-3/F)\pi(X)$ starts have $\lfloor F\rfloor$ successive good primes through $X$. At least $(1-\rho-3/F)\pi(X)$ have this property and diameter at most $2F\log X/(\rho\log 2)$. The proof uses the earlier global count and the elementary lower bound for $\pi(X)$. For ordered points in an interval of length $H$, one bad point removes at most $L$ starts of length $L$. Summed over all starts, the endpoint distances cost at most $(L-1)H$. The diameter bound follows by counting starts larger than the specified distance. [Finite deletion](ThetaPrimeRuns.lean) · [Total endpoint distances](ThetaRunDiameters.lean) · [Global prime result](ThetaShortPrimeDiameters.lean)

The explicit choice $F=\exp(\sqrt{\log y\,\log\log y}/8192)$ holds eventually for every fixed deviation. [Explicit-constant theorem](ThetaShortPrimeRuns.lean)

## All primes at Baker–Harman–Pintz length

Let \(H=\lfloor X^{21/40}\rfloor\). For every fixed \(c<1/2\) and \(\gamma<9/100\), every sufficiently large integer \(X\) satisfies
\[
  \#\{X<p\le X+H:\ p\ {\rm prime},\ S(p)>cp\log p\}
       \ge \gamma\,X^{21/40}/\log X .
\]
More precisely, for each fixed \(\varepsilon>0\), the fraction of the primes in that interval with \(\lvert S(p)-p\log p/2\rvert\ge\varepsilon p\log p\) is at most \((100/9)\exp(-\sqrt{\log X\log\log X}/2048)\), eventually. These assertions use the complete Weil bound for Kloosterman sums and the closing prime-count inequality of Baker, Harman and Pintz. Both published inputs are explicit hypotheses in Lean. The former controls theta exceptions and the latter supplies the ordinary prime count. [Positive primes and prime-normalized exception count](ThetaBHPIntervals.lean) · [Baker, Harman and Pintz, p. 562](https://www.cs.umd.edu/~gasarch/BLOGPAPERS/BakerHarmanPintz.pdf#page=31) · [Weil](https://doi.org/10.1073/pnas.34.5.204)

For arbitrary \(H\le X\), using just the complete Weil bound replaces the second term in the elementary exception bound below by \(C_\varepsilon\sqrt X(1+\log X)^8\). In particular, the stretched-exponential bound on the scale \(H/\log X\) applies uniformly once \(H\ge\sqrt X\exp(\sqrt{\log X\log\log X}/512)\). The published lower bound for \(H=\lfloor X^{21/40}\rfloor\) is \(9X^{21/40}/(100\log X)\); no asymptotic formula for the ordinary prime count at this length is needed. [Square-root exceptional bound](ThetaWeilShortIntervals.lean) · [Original arithmetic sum](https://arxiv.org/abs/2501.03234)

The centered model gives a stronger first term in every translated interval $(X,X+H]$, $H\le X$. For each fixed relative deviation $\varepsilon>0$, the exception count is at most
\[
 \frac{H}{\log X}\exp(-a_\varepsilon(\log X)^{3/4})+
 C_\varepsilon X^\theta(1+\log X)^8 .
\]
Here $\theta=3/4$ unconditionally, and $\theta=1/2$ with the complete Weil bound. Translation preserves the complete centered moment and each centered row period. The energy of the high rows supplies the endpoint-independent term. [Translated centered moment](ThetaCenteredMoment.lean) · [Short band](ThetaShortCenteredBand.lean) · [Both endpoint exponents](ThetaShortCenteredInterval.lean) · [Backward-window exceptions](ThetaCenteredBackward.lean)

## The elementary cutoff at three quarters

Fix \(c<1/2\). There is a constant \(K_c>0\) such that, for every sufficiently large integer \(X\), every integer length
\[
  K_c X^{3/4}(1+\log X)^9\le H\le X
\]
satisfies the following implication. If \((X,X+H]\) contains at least \(H/(2\log X)\) primes, at least \(H/(4\log X)\) of them satisfy \(S(p)>cp\log p\). Here \(S\) is the signed integer sum in the pinned DeepMind file. Taking \(c=0\) gives positive values in each such interval. The transfer and its prime-count hypothesis are stated in Lean as `ThetaShortPrimeInterval.good_count`. [Formal statement](ThetaShortPrimeInterval.lean) · [Pinned DeepMind problem](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean)

Guth and Maynard's Corollary 1.3 supplies the ordinary prime-count hypothesis throughout this range up to \(H=X^{0.99}\). Indeed \(17/30<3/4\), and their uniform error \(O_\eta(H\exp(-(\log X)^{1/4}))\) is \(o(H/\log X)\). This prime-count theorem is external to the Lean development. In particular, with \(H=\lceil K_c X^{3/4}(1+\log X)^9\rceil\), the original sum exceeds \(cp\log p\) at least \(H/(4\log X)\) times in every sufficiently far out interval \((X,X+H]\). The pointwise conjecture for all sufficiently large primes remains open. [Guth and Maynard, Corollary 1.3](https://arxiv.org/html/2405.20552v2#S1) · [Berndt, Bhat, Meyer, Xie and Zaharescu, §3](https://arxiv.org/pdf/2501.03234v3#page=4)

## A finite exception bound in every interval

Put \(R_X=\sqrt{\log X\log\log X}\). For fixed \(\varepsilon>0\), let \(E(X,H)\) count primes \(X<p\le X+H\) with \(\lvert S(p)-\tfrac12p\log p\rvert\ge\varepsilon p\log p\). There is a \(C_\varepsilon>0\) such that for all sufficiently large \(X\) and all \(0\le H\le X\),
\[
 E(X,H)\le {H\over\log X}e^{-R_X/1536}
        + C_\varepsilon X^{3/4}(1+\log X)^8.
\]
If \(X^{3/4}\exp(R_X/512)\le H\le X\), then \(E(X,H)\le (H/\log X)\exp(-R_X/2048)\). The same last bound holds for the one-sided exceptions \(S(p)\le cp\log p\) with fixed \(c<1/2\). All three exceptional-count estimates hold in Lean without a prime-count hypothesis. They control the location of the exceptions at a scale at which the global exceptional-set bound can exceed the length of a single interval. [Interval bounds](ThetaShortPrimeInterval.lean) · [Earlier global bound](STRONG-PRIME-TAIL.md)

## Why the spacing cost is linear in the largest denominator

Translation changes Fourier coefficients by phases of norm one. On a band of reduced denominators \(R\le q<2R\), the translated large sieve costs \(O(H+R^2\log(2Y))\) times the squared coefficient mass. For the \(H\) term, removing the rows up to \(T\) gives the uniform mass bound \(O(T^{-1/64})\). For the spacing term, each individual block has norm \(O((1+\log q)/q)\), so the entire band has squared mass \(O((1+\log(2Y))^2/R)\). The product of the quadratic spacing cost and this second estimate costs at most \(O(Y(1+\log(2Y))^3)\) on any band. These two simultaneous estimates retain decay in \(T\) on the interval-length term. [Translated large sieve](ThetaReciprocalLargeSieve.lean) · [Block mass and variance](ThetaShortIntervalMass.lean)

There are \(O(1+\log Y)\) bands. For \(Y=2J\le 2N^{52}\), Cauchy–Schwarz gives translated variance \(O((1+\log N)^5(H/T^{1/64}+J))\). The low rows up to \(T\) have a separate moment estimate uniform in the starting point, by expansion into products of short period. [Dyadic inequality](ThetaTranslatedVariance.lean) · [Variance with variable cutoff](ThetaShortIntervalEnergy.lean) · [Translated period means](ThetaIntervalPowerEndpoint.lean) · [Prime-band transfer](ThetaShortPrimeBand.lean)

For every prime in the common band \(N^{56}\le p\le N^{64}\), take \(b=1+\lfloor\log_2 N\rfloor\), \(J=N^{48}b^3\), and the largest odd width \(K\le N\). For a uniform complete-sum bound \(B\), the reciprocal parity discrepancy is at most \(2B(1+H_{\lfloor p/2\rfloor})^2\). On the 64th-power band one can thus use \(J=N^e b^3\) when all complete Kloosterman sums at nonzero reciprocal multiplier have norm at most \(2N^e\), for \(32\le e\le48\). Weil's square-root estimate takes \(e=32\); the elementary bound proved in the notebook takes \(e=48\). [Complete sums to reciprocal intervals](ThetaReciprocalCutoff.lean) · [Variable-cutoff cone](ThetaNondivisibleCone.lean)

At \(e=48\), the elementary reciprocal discrepancy is \(O(p^{3/4}(1+\log p)^2)\). Truncating denominators costs at most this times \(O(p(1+\log p)/J)\), together with a smaller divisor-count error. Thus the denominator cost is \(O(p)\) uniformly. The discarded numerator tail and the cotangent linearization also cost \(O(p)\) here. The resulting window controls the original normalized \(S(p)/p-\tfrac12\log p\) up to an absolute additive constant. Substitution in the variance bound costs three further powers of \(1+\log N\). Taking \(N^{64}\asymp X\) converts \(N^{48}\) to \(X^{3/4}\). [Calibrated cone and original-sum comparison](ThetaCalibratedCone.lean) · [Band deviation estimate](ThetaShortWindowDeviation.lean)

The indexed pointwise reductions and the OMA continued-fraction estimates address other aspects of the original question. [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [Digit-extraction identity](https://github.com/lefttosolve2/open-math-agents/pull/12097) · [OMA integral mean](https://github.com/lefttosolve2/open-math-agents/pull/27960) · [OMA fixed-depth limit](https://github.com/lefttosolve2/open-math-agents/pull/28015) · [Left to Solve solved index](https://lefttosolve.com/solved/step#step)
