# Bounded clusters of positive theta primes in the class one modulo eight

Fix \(m\ge1\). There are \(k,D,C_m,\beta_m>0\) such that, for each \(\varepsilon>0\), every sufficiently large \(X\) and every integer \(C_m X^{21/40}\le H\le X\) admit at least \(\beta_mH/(1+\log X)^k\) pairwise disjoint intervals \([n,n+D]\subset(X,X+H]\) with the following properties.

- Each interval contains at least \(m\) ordinary primes. **Every prime** in the interval is \(1\bmod8\).
- Every such prime satisfies \(\lvert S(p)-p\log p/2\rvert<\varepsilon p\log p\). Taking \(\varepsilon=1/2\) gives strict positivity throughout each run.

The primes in each interval form a consecutive block of the global prime sequence. Banks, Freiberg and Turnage-Butterbaugh proved the existence of arbitrarily long bounded runs in reduced residue classes. Here the theta estimate holds throughout disjoint runs in every indicated short interval. The ordinary-prime input is Alweiss–Luo, Theorem 1.1, and the theta exception input uses the complete Weil bound. Both appear explicitly in the Lean theorem. [Consecutive theta clusters](ThetaConsecutiveClusters.lean) · [Banks–Freiberg–Turnage-Butterbaugh](https://arxiv.org/abs/1311.7003) · [Alweiss–Luo](https://arxiv.org/pdf/1707.05437#page=4) · [Weil](https://doi.org/10.1073/pnas.34.5.204)

For an explicit progression, put \(D=1+8k!\,k\), \(C=8D!\), \(F_h=1+Ch\), and let \(Q\) be the product of the \(F_h\) over \(1\le h\le D\) with \(h\not\equiv1\bmod8\). Write \(Q=1+CT\). At each base \(N=8Qt+CT^2\), the identity
\[
 CT^2+h+T F_h=(T+h)Q
\]
makes \(F_h\) divide \(N+h\). Each forbidden offset is composite once the base is sufficiently large. The base itself is divisible by eight. Every prime divisor of \(Q\) exceeds \(D\). Such a prime dividing \(F_h\) cannot divide a target \(N+1+8k!j\), since its offset and \(h\) are distinct integers between zero and \(D\). At primes not dividing \(Q\), the change of variable \(t\mapsto Qt+D!T^2\) preserves admissibility. Applying the short-interval tuple estimate at slope \(8Q\) gives \(C_m=32Q\). If \(A\) is the sieve count constant, deletion and disjoint selection give \(\beta_m=A/[64Q(D+1)]\). [Explicit divisors and admissibility](ThetaConsecutiveProgression.lean) · [Affine interval transfer](ThetaAffineSieveInterval.lean)

## Fixed patterns and unbounded recurring gaps

The Alweiss–Luo ordinary prime-tuple count alone suffices for a dyadic conclusion. For each fixed \(m\) choose its admissible system of \(k\) forms. There are a fixed set \(T\subseteq\{0,\ldots,D\}\), \(|T|\ge m\), a constant \(\beta>0\), and an unbounded set of integer endpoints \(E\). For every \(\varepsilon>0\) and every sufficiently large \(X\in E\), at least \(\beta X/(1+\log X)^k\) bases \(n\) in \((X,2X-D]\) have exactly \(T\) as the prime offsets of \([n,n+D]\). All its primes are \(1\bmod8\) and satisfy \(\lvert S(p)-p\log p/2\rvert<\varepsilon p\log p\). The same \(T\) and \(E\) work for every accuracy. Along one strictly increasing sequence of bases, all the normalized values \(S(n+j)/((n+j)\log(n+j))\), \(j\in T\), converge to \(1/2\). One picks a frequent ordinary pattern before deleting the bases meeting a theta exception. The global exceptional count makes this deletion \(o(X/(\log X)^k)\) for each fixed accuracy. [Pattern selection and simultaneous convergence](ThetaRecurringPrimePattern.lean) · [Alweiss–Luo, Theorem 4.1](https://arxiv.org/pdf/1707.05437) · [Global exception estimate](STRONG-PRIME-TAIL.md)

Consequently there are arbitrarily large fixed multiples \(g\) of eight for which infinitely many pairs \(p,p+g\) are consecutive ordinary primes, both \(1\bmod8\), and the normalized theta values at both endpoints tend to \(1/2\) on the same sequence. Given \(G\), take \(m=(G+2)!+G+4\). In one realization of the fixed pattern, let \(B\) be the next multiple of \((G+2)!\) beyond its first prime. Each of \(B+2,\ldots,B+G+2\) is composite and the pattern extends beyond that block. The adjacent offsets straddling it give one fixed \(g>G\) in every subsequent realization. The theorem leaves the individual gap values unspecified. Banks, Freiberg and Turnage-Butterbaugh previously proved recurring patterns of consecutive ordinary primes in reduced residue classes. The theta statement here adds simultaneous convergence for the original signed sum. [Fixed gaps with common theta limits](ThetaUnboundedPrimeGaps.lean) · [Banks–Freiberg–Turnage-Butterbaugh](https://arxiv.org/abs/1311.7003)

## The uniform length constant with other intervening classes allowed

Fix \(m\ge1\) and \(\varepsilon>0\). Under the Alweiss–Luo short-interval tuple estimate and the complete Weil bound, there are \(k,D\) and \(\beta>0\) such that every sufficiently large \(X\) and every integer \(32 X^{21/40}\le H\le X\) admit at least \(\beta H/(1+\log X)^k\) **pairwise disjoint** integer intervals \([n,n+D]\subset(X,X+H]\). Each contains at least \(m\) primes congruent to \(1\bmod8\). Every prime \(p\) in each interval, including the intervening primes in other classes, satisfies
\[
 \left|S(p)-\tfrac12 p\log p\right|<\varepsilon p\log p.
\]
For \(\varepsilon\le1/2\) every such prime has positive \(S(p)\). The sign at every sufficiently large prime in the class remains open. [Disjoint clusters for the pinned sum](ThetaShortPositiveClusters.lean) · [Original definition](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean)

The ordinary-prime input is Alweiss–Luo’s Theorem 1.1 at \(\delta=21/40\), specialized to the admissible forms \(8t+1+8k!j\). Its count on \([z-y,z]\) carries the additional condition that every form has large least prime factor, which we may discard. With \(y=\lfloor H/16\rfloor\) and \(z=\lfloor X/8\rfloor+1+y\), the lemma verifies \(z^{21/40}\le y\) and injects the sieve bases into \((X,X+H-D]\) by \(t\mapsto8t\). If \(A\) is the lower-count constant in Lean’s ordinary sieve hypothesis, the proof retains \(A/32\) after dilation and \(A/64\) after removing bad bases. [Alweiss–Luo, Theorems 1.1 and 4.1](https://arxiv.org/pdf/1707.05437#page=4) · [Endpoint transfer and exact ordinary input](ThetaShortAffineTuples.lean)

One theta-exceptional prime rules out at most \(D+1\) bases. The square-root error estimate obtained from Weil makes the number discarded at most \(\eta H/(1+\log X)^k\) for every fixed \(\eta>0\) at this length. Keeping the most frequent residue of the surviving bases modulo \(D+1\) makes their closed intervals disjoint and loses at most a factor \(D+1\). This gives \(\beta=A/[64(D+1)]\). Both ordinary-prime and complete-sum estimates are explicit Lean hypotheses. [Weil](https://doi.org/10.1073/pnas.34.5.204) · [Exception estimate](ThetaWeilShortIntervals.lean) · [Deletion and packing](ThetaShortPositiveClusters.lean)

## Longer intervals from Maynard’s sieve

Fix an integer \(m\ge1\) and \(c<1/2\). There are integers \(k,D\) depending on \(m\) and positive constants \(K,\beta\) such that, for all sufficiently large integers \(X\), every integer \(H\) with
\[
  2D\le H\le X,\qquad KX^{3/4}(1+\log X)^{8+k}\le H
\]
has at least \(\beta H/(1+\log X)^k\) different bases \(X<n\le X+H-D\) with both properties below.

- At least \(m\) primes in \([n,n+D]\) are \(1\bmod 8\).
- Every prime \(p\) in \([n,n+D]\) satisfies \(S(p)>cp\log p\), including primes in the other residue classes.

Each entire cluster is contained in \((X,X+H]\). The count is of bases, so clusters may overlap. At \(c=0\) this gives bounded clusters of positive values in the residue class where the notebook's mod-eight congruence permits zero. Taking \(m=2\) gives infinitely many pairs at bounded distance in that class. The sign of \(S(p)\) at every individual prime remains open. [Original-sum theorem](ThetaMaynardClusters.lean) · [Pinned definition and conjectures](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean) · [Berndt et al.](https://arxiv.org/abs/2501.03234)

## The ordinary-prime input

The Lean theorem `ThetaMaynardClusters.original` takes `TupleCount m k α` and \(\alpha>0\) as explicit hypotheses and gives \(\beta=\alpha/128\). Maynard's Theorem 3.4, with \(\varepsilon=1/24\), supplies \(k\) and such an \(\alpha\) for the fixed admissible forms
\[
 L_j(t)=8t+1+8k!\,j,\qquad 0\le j<k.
\]
These are distinct primitive linear forms with fixed coefficients. For \(x^{5/8}\le y\le x\) the theorem counts \(\gg y/(\log x)^k\) integers \(t\in[x,x+y]\) at which at least \(m\) forms are prime. This implies the precise Lean input with \(1+\log x\) in the denominator. Maynard's sieve proof is external. Admissibility, the map from prime indices to distinct primes, the dilation of the interval and the signed-theta transfer are all proved in Lean. [Maynard, Theorem 3.4](https://arxiv.org/pdf/1405.2593#page=3) · [Admissibility and explicit hypothesis](ThetaMaynardClusters.lean)

For admissibility at a prime \(q\), set \(A=8k!\). If \(q\mid A\), then \(t=0\) works. Otherwise \(q>k\) and \(8\) is invertible modulo \(q\). Choose \(8t=A-1\bmod q\). Then \(L_j(t)=A(j+1)\bmod q\) is nonzero for each \(j<k\). All the primes in the tuple lie in \([8t,8t+D]\) with \(D=1+8k!\,k\). To place the bases in \((X,X+H]\), use \(x=\lfloor X/8\rfloor+1\) and \(y=\lfloor H/16\rfloor\). For \(H\ge X^{2/3}\) these satisfy \(y\ge x^{5/8}\) eventually and \(y\ge H/32\). Applying the transfer at length \(H-D\) leaves room for the right endpoint of the last cluster. [Interval dilation and containment](ThetaAffineClusters.lean)

## How many clusters can an exception destroy?

Set \(\varepsilon=1/2-c\). A prime with \(\lvert S(p)-\tfrac12p\log p\rvert\ge\varepsilon p\log p\) can belong to \([n,n+D]\) for at most \(D+1\) integer bases \(n\). Apply the notebook's two-term short-interval bound to \((X,X+H+D]\). With \(R_X=\sqrt{\log X\log\log X}\), the number of affected bases is
\[
 \ll_D (H/\log X)e^{-R_X/1536}
      + O_{\varepsilon,D}\big(X^{3/4}(1+\log X)^8\big)
\]
when \(D\le H\) and \(H+D\le X\). The first term is smaller than any fixed multiple of \(H/(1+\log X)^k\) eventually. The second is smaller than the required fraction of the ordinary sieve count as soon as \(H\ge K X^{3/4}(1+\log X)^{8+k}\), with \(K\) chosen for that fraction. Removing affected bases retains the original strict inequality for every prime in each remaining interval. [Finite deletion bound](ThetaPrimeClusterTransfer.lean) · [Strict lower bound for \(S\)](ThetaClassOneClusters.lean) · [Short-interval exception estimate](SHORT-PRIME-INTERVALS.md)

The live DeepMind pointwise reduction, OMA work on the congruence and cotangent obstructions, and the Left to Solve index were checked for overlap. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA congruence reduction](https://github.com/lefttosolve2/open-math-agents/pull/12031) · [OMA asymptotic reduction](https://github.com/lefttosolve2/open-math-agents/pull/21388) · [LTS solved index](https://lefttosolve.com/api/solved)
