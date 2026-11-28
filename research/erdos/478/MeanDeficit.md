# A positive upper proportion of primes with missing factorial residues

Let $A_p=\{k!\bmod p:1\leq k<p\}$ and $\delta_p=p-|A_p|$. At arbitrarily large cutoffs $X$, at least one in 325 primes $p\le X$ has $\delta_p\ge6$. More generally, for each integer $D\ge1$ there are arbitrarily large $X$ such that
$$
\#\{p\le X:p\text{ prime},\ \delta_p\ge D\}\ \ge\ \frac{\pi(X)}{54D+1}.
$$
The earlier notebook result gave a sublinear power-law count for fixed thresholds in progressions. The proportion bound here concerns all primes. [Lean proof](Erdos478MeanDeficit.lean) · [Earlier counting result](SplittingFrequency.md)

With reciprocal-prime weights the quantifier is stronger. For every fixed $D\ge1$ and **all sufficiently large** $X$,
$$
\sum_{\substack{p\le X\\\delta_p\ge D}}\frac1p
\ \ge\ \frac1{54D}\sum_{p\le X}\frac1p .
$$
Both sums run over primes. The prime-harmonic mean $\sum_{p\le X}\delta_p/p\,/\,\sum_{p\le X}1/p$ tends to infinity. The prime-count and harmonic-proportion theorems leave the threshold-dependent cutoff unspecified.

## Where the bound comes from

1. For a monic $f\in\mathbb Z[x]$ irreducible over $\mathbb Q$, adjoin one root. Away from the conductor of the resulting order, Kummer–Dedekind identifies the degree-one prime ideals over $p$ with the distinct roots of $f$ modulo $p$. The number of integral ideals of norm at most $x$ is asymptotic to a positive constant times $x$. Each sufficiently large dyadic shell therefore contributes at least a fixed positive amount to their reciprocal-norm sum.
2. Unique factorization of ideals bounds that sum by a finite Euler product. In its logarithm, a degree-one prime contributes at most $1/p+2/p^2$ and a higher-degree prime at most $2/p^2$. At most $[K:\mathbb Q]$ primes lie above $p$, so the errors have bounded total. Writing $r_f(p)$ for the number of distinct roots gives $\sum_{p\le2^n}r_f(p)/p\ge\log n-O_f(1)$. The field affects the error and the cutoff. The coefficient of $\log n$ is one. [Prime-ideal argument](Erdos478PrimeIdealMass.lean)
3. Apply this estimate to the gap lengths $k=2,\ldots,L+1$. The falling-factorial polynomial $x(x-1)\cdots(x-k+1)-1$ is irreducible over $\mathbb Q$. Away from finitely many primes, roots for different lengths give distinct upper endpoints of factorial collisions. Their sum is bounded by both $\delta_p$ and $M=\sum_{k=2}^{L+1}k$. Thus the harmonic sum of $\min(\delta_p,M)$ has leading coefficient at least $L$ on the dyadic scale. [Disjoint gap endpoints](DisjointGapFamilies.md)
4. Chebyshev's bound for $\sum_{p\le x}\log p$ gives $\sum_{p\le2^n}1/p\le5+4\log n$. Taking $L=8D+1$ makes $M\le54D^2$ and ensures that the weighted truncated mean eventually reaches $2D$. At primes below the threshold the contribution is at most $D$. The remaining primes must carry at least $1/(54D)$ of the harmonic weight. Partial summation converts this all-cutoff bound into the stated ordinary count at arbitrarily large cutoffs.

## Scope, prior work and verification

`Erdos478.MeanDeficit.frequently_many_deficit_primes` gives the ordinary count, `harmonic_proportion` gives the reciprocal-weight inequality, and `harmonic_mean_deficit` gives the divergent mean. The Lean definition of `deficit` subtracts the cardinality of the literal pinned factorial image from $p$. The upstream declaration asks for $|A_p|/p\to1-1/e$ along every prime. These results control fixed deficits and their frequency. [Pinned Erdős 478](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean)

Klurman and Munsch use the same irreducible gap polynomials and degree-one prime ideals in their quantitative theorem for the ordinary average deficit. Banks, Luca, Shparlinski and Stichtenoth established a growing deficit along infinitely many primes. The contribution here is the checked harmonic and ordinary threshold bounds with explicit constants. The proof uses the pinned ideal-counting asymptotic and finite Euler products throughout. [Klurman–Munsch, §2](https://www.numdam.org/item/10.5802/jtnb.974.pdf) · [Banks et al. (2005)](https://journals.tubitak.gov.tr/math/vol29/iss2/6/)

The live overlap check on 2026-11-28 found the DeepMind statement issue and PR, the open and unclaimed Left to Solve target, and OMA factorial matches for a sum and a divisor count. Independent Lean 4.33.1 replay covers both new modules and their two notebook dependencies. All 28 printed declarations use only `propext`, `Classical.choice` and `Quot.sound`. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [DeepMind statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5229) · [Left to Solve](https://lefttosolve.com/p/Erdos478.erdos_478) · [OMA factorial sum](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4056) · [OMA divisor count](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7450) · [Notebook replay](../../README.md#replay)
