# Many factorial-deficit primes below every large cutoff

Let $A_p=\{j!\bmod p:1\le j<p\}$, and let $F_p=p-1-|A_p|$ count the missing nonzero residues. Write $T=\log\log X$. For every $\varepsilon>0$ there is a $c>0$ such that, at every sufficiently large natural cutoff $X$,
$$
\#\left\{p\le X:p\text{ prime},\quad F_p\ge
  \frac{T}{\log T-\log\log T+\varepsilon}\right\}
\ \ge\ \exp\!\left(\exp\!\left(c\frac{T}{\log T}\right)\right).
$$
The threshold uses $X$ even for primes much smaller than $X$. One can choose at least that many primes and a common $n=n(X)$ with $2n$ at least this threshold. Modulo each chosen prime, every even gap polynomial of length $2,4,\ldots,2n$ has two distinct roots. The product of these polynomials is separable modulo each witness prime. Their roots therefore give at least $2n$ distinct endpoints of repeated factorial residues. [Abundance and deficit theorems](Erdos478AbundantFactorialDeficit.lean) · [Gap predicate and endpoint count](Erdos478EvenGapFamily.lean)

For example, modulo 241 the upper endpoints are 52 and 190 at length 2, 28 and 216 at length 4, and 93 and 153 at length 6. Each endpoint $z$ satisfies $z!\equiv(z-k)!\pmod{241}$ for its listed length $k$. These six endpoints certify six missing nonzero residues. Direct enumeration gives $|A_{241}|=146$ and $F_{241}=94$.

## Counting primes by excluding a product

Fix $n\ge1$ and an integer $L\ge0$. Put $b=2n+4$ and $W=2^{b^{2n+19}(L+1)^2}$. More than $2^L$ distinct witness primes lie below or at $W$. If there were at most $2^L$ of them, their product $C$ would satisfy $1\le C\le W^{2^L}$. Applying the sieved common-root construction with $C$ as an extra excluded factor supplies a witness prime $p\le W$ with $p\nmid C$. [Finite multiplicity bound](Erdos478ManyEvenWitnesses.lean) · [Product argument](Erdos478AvoidanceCount.lean)

The sieve charges the extra factor through a double logarithm. In particular $C\le2^{2^\ell}$ raises the bit budget by at most $\ell+3$. The exponent in the Schur prime bound grows at most quadratically in that bit budget, which gives the $(L+1)^2$ factor in $W$. [Cost of exclusion](Erdos478ExclusionBits.lean) · [Schur exponent](Erdos478SievedEvenScale.lean)

Choose an integer $d>16/\varepsilon$ and put $L=2^{\lfloor n/d\rfloor}$. Use the largest $n$ whose ceiling
$$
2^{(2n+4)^{2n+19}\,2^{\,2\lfloor n/d\rfloor+2}}
$$
is at most $X$. Its successor gives
$$
T \le (2n+21)\log(2n+6)
       + (2\lfloor(n+1)/d\rfloor+2)\log 2 .
$$
The final term is at most $\varepsilon(2n)/4$ once $n\ge2d$. Logarithmic inversion gives the stated threshold, and converting $2^L$ to natural exponentials gives the count with $c=1/(16d)$. [Cutoff and successor](Erdos478AbundanceCutoff.lean) · [Rate estimates](Erdos478AbundanceRate.lean) · [Inversion](Erdos478SievedLogInversion.lean)

## Relation to Erdős 478

Banks, Luca, Shparlinski and Stichtenoth proved a growing deficit with leading constant one on a prime subsequence. Klurman and Munsch proved an unconditional lower bound of order $\log\log X/\log\log\log X$ for the prime **mean** deficit. Here the conclusion counts individual primes at a specified growing threshold and supplies common gap lengths for them. The notebook previously checked a single bounded simultaneous witness and a density-one theorem at every **fixed** deficit threshold. [Banks et al., Theorem 3](https://journals.tubitak.gov.tr/math/vol29/iss2/6/) · [Klurman and Munsch, Theorem 2.1](https://www.numdam.org/article/JTNB_2017__29_1_169_0.pdf) · [Single bounded witness](SievedFactorialDeficit.md) · [Fixed thresholds](FactorialDeficitDensity.md) · [Power intervals at fixed threshold](DeficitPowerIntervals.md)

The count lower bound divided by $\pi(X)$ tends to zero. The relative frequency at this growing threshold and the upstream limit $|A_p|/p\to1-1/e$ along all primes remain undetermined by this result. The live and pinned upstream statement files had the same Git blob on 2026-11-28. The DeepMind search found the statement additions, Left to Solve listed the problem as open, and the OMA search for the declaration returned no match. [Pinned statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/4078) · [Tracking issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [Left to Solve](https://lefttosolve.com/p/Erdos478.erdos_478) · [OMA declaration search](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=Erdos478)

The Lean 4.33.1 replay compiles 29 local modules for the abundance theorem and two more for the earlier endpoints, compares the image and prime condition directly with the pinned declaration, and checks each module in a separate kernel process. The 79 printed declarations, including 32 named checks, use only `propext`, `Classical.choice` and `Quot.sound`. [Notebook replay](../../README.md#replay)
