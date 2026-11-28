# Counting primes with missing factorial residues

Let $A_p=\{n!\bmod p:1\le n<p\}$. For example, at arbitrarily large cutoffs $X$, more than $X^{1/721}$ primes $p<X$ miss at least six residues. The general result counts primes in a prescribed progression and allows every fixed triangular deficit. [Lean proof](Erdos478SplittingFrequency.lean)

Fix $m\ge1$ and $L\ge0$. Set
$$D=\binom{L+2}{2},\qquad h=D-1+\varphi(m),\qquad E=h!.$$
Let $W(X)$ count primes $p<X$ for which $m\mid p-1$ and $p-|A_p|\ge D$. For every real $r>E$ and every cutoff $N$, there is an integer $X>N$ with
$$X<W(X)^r.$$
The reciprocal-power series $\sum_p p^{-1/E}$ over the same witnesses diverges. Taking $m=1$, $L=2$ gives $D=6$ and $E=720$. The earlier result proved the existence of arbitrarily large individual witnesses. [Earlier progression theorem](DisjointGapFamilies.md)

## Why there are this many witnesses

For a monic integer polynomial $g$ of degree $d>0$, consider the primes dividing its nonzero values at natural numbers. Suppose their $p^{-1/d}$ weights summed to a finite value. A finite Euler product then gives a uniform bound for the sum of $n^{-1/d}$ over positive integers supported on those primes. Indeed, for $s>0$ and a finite prime set $P$, the product of $(1-p^{-s})^{-1}$ over $P$ is at most $\exp((1-2^{-s})^{-1}\sum_{p\in P}p^{-s})$.

On a tail, $g(n)$ is positive, strictly increasing, and at most $2n^d$. Its values alone would therefore contribute at least a positive constant times the harmonic series. This contradiction proves divergence at $s=1/d$.

The test polynomial $t$ for the factorial problem is the product of the falling-factorial gap polynomials of lengths $2,\ldots,L+1$ and the cyclotomic polynomial $\Phi_m$. It has degree $h$. Its splitting field acts faithfully on at most $h$ roots, so its degree is at most $E$. The minimal polynomial of an integral primitive generator has that field degree. Outside a finite cutoff, a prime divisor of one of its values yields a specialization of the ring of integers to $\mathbf F_p$, and $t$ splits completely there. The gap roots give distinct repeated factorial endpoints, and $\Phi_m$ supplies the progression condition. [Splitting test](Erdos478UnboundedDeficit.lean) · [Factorial endpoint count](Erdos478DisjointGapFamilies.lean)

Finally, if $X<W(X)^r$ failed for all sufficiently large $X$, the $j$th witness would be at least $j^r$ for large $j$, with indexing from zero. Its $p^{-1/E}$ weight would be at most $j^{-r/E}$. This last series converges whenever $r>E$.

## Scope and verification

`Erdos478.SplittingFrequency.many_deficit_primes` uses the same finite image as the pinned `Erdos478.erdos_478`. It gives a power lower bound at arbitrarily large cutoffs. The conjectured limit $|A_p|/p\to1-1/e$ along all primes remains open. [Pinned statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean)

Banks, Luca, Shparlinski and Stichtenoth proved a growing deficit in terms of the prime. Klurman and Munsch proved a quantitative average deficit. Classically, Chebotarev also gives positive density among primes for complete splitting in a fixed Galois field. The contribution here is a Lean proof of the explicit counting and divergence bounds for the factorial witness predicate, using polynomial values and finite Euler products. [Banks et al.](https://journals.tubitak.gov.tr/math/vol29/iss2/6/) · [Klurman and Munsch, §2](https://www.numdam.org/item/10.5802/jtnb.974.pdf) · [Conrad on splitting-prime density](https://math.stanford.edu/~conrad/676Page/handouts/dirdensity.pdf) · [Separate Chebotarev formalization](https://github.com/cbirkbeck/chebotarev-density)

The 2026-11-28 overlap check found the DeepMind statement issue and PR, the open Left to Solve target, and OMA matches for a factorial sum and a divisor count. The proof and its two notebook dependencies passed a clean Lean 4.33.1 build with warnings as errors and independent `leanchecker` replay. All 23 printed declarations use only `propext`, `Classical.choice` and `Quot.sound`. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5229) · [Left to Solve](https://lefttosolve.com/p/Erdos478.erdos_478) · [OMA factorial sum](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4056) · [OMA divisor count](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7450) · [Replay instructions](../../README.md#replay)
