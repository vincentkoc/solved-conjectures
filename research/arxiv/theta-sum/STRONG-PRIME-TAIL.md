# A three-quarter-power exceptional bound for the original theta sum

For every fixed $\varepsilon>0$ there is $a_\varepsilon>0$ such that every sufficiently large integer $X$ satisfies
\[
 \frac{\#\{p\le X:\ p\ \mathrm{prime},\
    |S(p)-\tfrac12p\log p|\ge\varepsilon p\log p\}}{\pi(X)}
 \le \exp\!\left(-a_\varepsilon(\log X)^{3/4}\right).
\]
For every fixed $c<1/2$ the same form of estimate holds for $S(p)\le c p\log p$. At $c=0$ this counts all nonpositive prime values. For the canonical lower assertion there is a single $a>0$ such that, for every $n\in\mathbb N$, the number of odd primes through $X$ with $S(p)\le np$ is at most $M_n+\pi(X)\exp(-a(\log X)^{3/4})$ eventually. The coefficient $a$ is independent of $n$ because $np\le \frac14p\log p$ once $\log p\ge4n$. [Original-sum theorem, lower coefficients and canonical failures](ThetaCenteredOriginalTail.lean)

The uncentered moment argument also gives the explicit bound $\pi(X)\exp(-\sqrt{\log X\,\log\log X}/2048)$ for the two-sided count, with the same constant for every fixed $\varepsilon$ and a starting endpoint depending on $\varepsilon$. The earlier notebook bound saved $\exp(-a_c\sqrt{\log X})$ for each $c<1/2$. [Explicit constant](ThetaStrongOriginalTail.lean) · [Earlier estimate](PRIME-CONCENTRATION.md)

$S$ is the signed integer double sum in the pinned source. Both estimates allow infinitely many exceptions. Positivity at every odd prime and the eventual lower bound at every odd prime remain open. These are Conjectures 1.1 and 4.4 in the pinned Lean file. The paper's v3 lower growth assertion is Conjecture 3.3. [Pinned definitions and hypotheses](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean) · [Berndt, Bhat, Meyer, Xie and Zaharescu, §3](https://arxiv.org/pdf/2501.03234v3#page=4)

## Removing the small-prime average

For a denominator cutoff $T$, let $P=T!$. At level $U$, take the product $m$ of the complete prime powers in $P$ whose primes are at most $U$. For a row model $G$ and any integer $n$, average $G(nv)$ over units $v\bmod P$ with $v\equiv1\bmod m$. Write this average as $A_U G(n)$. On the units, multiplication identifies the kernel with the fiber of the reduction map. The conditional-mean bound and multiplicative-orbit identity give $|A_U G(n)|\ll(\log U)^2$ on every residue. [Translation on a fiber and uniform bound](ThetaOrbitProjection.lean)

Put $Z_U=G-A_U G$. Each finer conditional average of $Z_U$ is the corresponding average of $G$ minus $A_U G$. The sibling oscillations are unchanged, and the initial value at level $U$ is zero. For all sufficiently large $U$, averaging over a full period therefore gives $\mathbb E\exp(U^{1/4}|Z_U|)\le 2e^J$ with an absolute constant $J$. Each centered row retains its own period $d$. This gives the finite-interval estimate
\[
 \sum_{n<X} Z_U(n)^j \ \le\ 2X e^J(j/U^{1/4})^j+2(12 Z T^2)^j,
 \qquad Z=\sum_{m\ge1}m^{-2}.
\]
In particular, the large modulus $m$ does not enter the endpoint term. [Centered exponential moment](ThetaCenteredExposure.lean) · [All residues](ThetaCenteredWindow.lean) · [Finite centered moment](ThetaCenteredMoment.lean)

Write $L=\log N$ on the band $N^{56}\le p\le N^{64}$. Choose $T=\lceil\exp(L^{3/4})\rceil$, $k=\lceil L^{1/4}\rceil$, and $U=\lceil\exp(d_\varepsilon\sqrt L)\rceil$. Taking $d_\varepsilon>0$ sufficiently small keeps the coarse average within the allowed deviation of order $\varepsilon L$. The high-denominator variance saves $T^{-1/64}$. At moment order $2k$ the factor $U^{-k/2}$ gives a saving of order $\exp(-c_\varepsilon L^{3/4})$. The product periods contribute at most $2e^{16L}$ to the count, which has scale $N^{64}$. One band covers the large primes below any endpoint; the elementary lower bound for $\pi(X)$ absorbs its logarithmic normalization cost. [Finite band count](ThetaCenteredPrimeBand.lean) · [Integer parameter choice](ThetaCenteredScales.lean) · [Band estimate](ThetaCenteredDeviation.lean) · [Endpoint transfer](ThetaCenteredEndpoint.lean)

## Moments on all residue classes

Let $G_{T,W}(n)$ be the sum of the reciprocal rows of denominators $2\le d\le T$ for a numerator window $W$. The width of each row and the cutoff in its common coefficient are arbitrary. The conditional exponential-moment estimate on the units modulo $T!$ holds uniformly over these windows. To include a nonunit $n$, discard every row with $(d,n)>1$, whose wave vanishes. Choose a unit modulo $T!$ agreeing with $n$ modulo the least common multiple of the remaining $d$. Multiplication by this unit permutes the reduced residues. Summing first on each orbit, then over all residues, gives absolute $a,K>0$ with
\[
 \frac1{T!}\sum_{x\bmod T!}\exp(a|G_{T,W}(x)|)\le K .
\]
[Masking identity and orbit average](ThetaAllWindowMoments.lean) · [Window-uniform exponential moment on units](ThetaModelExponentialMoment.lean)

For the finite interval, expand the $j$th power into products of $j$ rows. Each product has period dividing the least common multiple of its denominators, hence at most $T^j$. A weighted row is bounded in absolute value by $6Z$, where $Z=\sum_{m\ge1}m^{-2}$. There are at most $T^j$ products. For $T\ge2$ and integers $Y,j\ge0$ this gives
\[
 \sum_{n<Y}G_{T,W}(n)^j
 \le Y K(j/a)^j+2(6ZT^2)^j.
\]
The complete moment uses $x^j\le (j/a)^j e^{a|x|}$. The endpoint uses the short product periods even when $T!$ exceeds $Y$. [Product expansion and endpoint](ThetaWindowPowerEndpoint.lean) · [Finite moment](ThetaWindowFiniteMoments.lean)

## The explicit-constant estimate

Write $R(p)=S(p)/p-\frac12\log p$. For $N^{56}\le p\le N^{64}$, integers $2\le T\le2N^{52}$, $k\ge0$ and $u>0$, the number of primes satisfying $|R(p)|\ge C+(8/\pi^2)(u+1)$ is at most
\[
 \frac{BN^{64}}{T^{1/64}}
 +(N^{64}+1)K\left(\frac{2k}{au}\right)^{2k}
 +2\left(\frac{6ZT^2}{u}\right)^{2k}.
\]
The first term comes from the variance of the rows with $d>T$. The other terms use the even moment of the remaining rows. All four constants $B,C,K,a$ are independent of $N,T,k,u$. [Finite count in the original sum](ThetaWindowPrimeBand.lean)

Put $L=\log N$ and $H=\sqrt{L\log L}$. Take $T=\lceil e^H\rceil$, $k=\lceil\sqrt{L/\log L}\rceil$, and $u=bL$ with a fixed $b>0$ chosen for the deviation $\varepsilon$. For sufficiently large $N$, the three terms above are at most $BN^{64}e^{-H/64}$, $(N^{64}+1)K e^{-H/2}$, and $2e^{16L}$, respectively. To reach an arbitrary endpoint $X$, one band with $X\le N^{64}\le2^{64}X$ suffices. The primes below $N^{56}$ contribute at most $N^{56}$. The eventual Chebyshev lower bound for $\pi(X)$ absorbs the remaining logarithm. The proof uses neither a prime number theorem in progressions nor a hypothesis on the distribution of the exceptional primes. [Integer parameter choice](ThetaGrowingWindowScales.lean) · [Band estimate](ThetaStrongDeviation.lean) · [Endpoint comparison](ThetaStrongPrimeTail.lean)

The DeepMind issue reduces the conjectures to a pointwise remainder. Left to Solve and OMA index partial results for the congruence and the additive harmonic bound. The estimate here counts deviations of the original signed sum over primes. [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA finite linear bound](https://github.com/lefttosolve2/open-math-agents/pull/31296) · [OMA harmonic estimate](https://github.com/lefttosolve2/open-math-agents/pull/22818) · [Left to Solve solved index](https://lefttosolve.com/solved/step#step)
