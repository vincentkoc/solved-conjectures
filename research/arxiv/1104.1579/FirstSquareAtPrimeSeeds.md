# The first square factor in a Cunningham prefix product

For either Cunningham recurrence, let $T_0(p)=p$ and $P_k(p)=\prod_{0\le i<k}T_i(p)$. Use the normalized logarithmic Dirichlet mass on prime seeds,
\[
 \mu(A)=\lim_{s\downarrow1}(s-1)\sum_{\substack{p\in A\\p\ {\rm prime}}}\frac{\log p}{p^s}.
\]
The two recurrences give the same probability law for the first site at which the running product acquires a square factor. If $\delta_k=\mu\{p:P_k(p)\text{ is squarefree}\}$, then $\delta_1=1$, every $\delta_k$ is positive, and adjoining site $k\ge1$ removes exactly $\delta_k-\delta_{k+1}>0$ of the mass. These differences sum to one. A square can come from two terms. For example, $19,39,79,159$ are individually squarefree, and their product is divisible by $3^2$. [Euler product and site masses](CunninghamSquarefreeEulerDensity.lean) · [Normalization and tail](CunninghamSquarefreeWaitingTime.lean)

## Local factors

For an odd prime $q$, let $d=\operatorname{ord}_q(2)$ and $x_+=\max(x,0)$. The number of reduced residues modulo $q^2$ excluded by the first $k$ sites is
\[
 N_q(k)=(\min(k,d)-1)_+ +(q-1)\big(\min(d,(k-d)_+)-1\big)_+ .
\]
The Euler factor is $1-N_q(k)/(q(q-1))$. The factor at two is one. Their product over all primes converges to $\delta_k$. In particular, for $k\ge1$ and odd $q>2^k$, $N_q(k)=k-1$. [Local count](CunninghamSquarefreeLocalFactors.lean) · [Positive Euler limit](CunninghamSquarefreeEulerDensity.lean)

Once a site $i$ is divisible by $q$, the divisible sites are exactly those congruent to $i$ modulo $d$. The site-zero residue is excluded from the units. Each other first visit forbids the unique lift on which its term vanishes modulo $q^2$. A second visit in the prefix forbids all $q$ lifts. At $q=3$, for example, there is one bad reduced residue for $k=3$, and there are three for $k=4$. [Canonical term formulas](CunninghamSquarefreePrimeSeeds.lean) · [Repeated visits](CunninghamSquarefreeLocalFactors.lean)

## The limiting law

For a finite set of prime squares, the Chinese remainder theorem combines the reduced classes, and the prime Dirichlet series gives each combined class mass $1/\varphi(m)$. Taking the cutoff $L$ above $2^k+2$ ensures that a prime larger than $L$ cannot hit two sites in the prefix. The Selberg estimate bounds the omitted normalized mass eventually by every number strictly above $1632k/L$ as $s$ decreases to one. This justifies taking the infinite product. [Finite CRT and mass](CunninghamSquarefreePrimeMass.lean) · [Large-square bound](CunninghamSquarefreeAtPrimes.lean) · [Limit proof](CunninghamSquarefreeEulerDensity.lean)

For every sufficiently large integer $n$ the survival mass satisfies
\[
 \delta_{32n^2}\le \exp\!\left(-\frac{n\log 2}{16\log(16n^2)}\right).
\]
For $q\le16n^2$, every occupied class repeats within $32n^2$ sites. Every odd prime of order at most $n$ divides the product of the first $n$ Mersenne numbers. Their total logarithmic weight is small enough that Chebyshev's lower bound leaves a positive proportion of the weight at primes of order greater than $n$. Those primes supply the exponential bound. In particular, $\sum_{k\ge1}k^m\delta_k$ is finite for every nonnegative integer $m$. The first-obstruction masses are bounded by the survival masses, so they too have finite moments of every order. [Order estimate](CunninghamSingularSeriesGrowth.lean) · [Tail and moments](CunninghamSquarefreeWaitingTime.lean) · [Mathlib's Chebyshev bounds](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Chebyshev.lean)

## Scope and replay

The main declarations in `CunninghamChain.SquarefreeDensity` are `squarefree_prefix_mass`, `first_square_mass`, `prefixDensity_succ_lt`, `prefixDensity_tail`, `summable_prefixDensity_moments` and `first_square_total`. DeepMind's exact-length predicates require every prefix term to be prime and the successor to be nonprime. Their unrestricted infinitude assertions remain open. The earlier prime-seed theorem gives infinitely many examples with a prescribed terminal square and arbitrarily rough prefix. Here the distribution concerns the first square in the running product. [Pinned predicates](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean) · [Jones](https://arxiv.org/abs/1104.1579) · [Earlier prime-seed theorem](SquarefreePrefixesAtPrimeSeeds.md)

Squarefree values at prime arguments have an established sieve literature. Pastén treats a broader class of polynomials. Searches of DeepMind and Open Math Agents issues and PRs, including closed work, and 6,134 Left to Solve records found the original problem and its reductions. No matching formalization appeared in those searches. [Pastén](https://people.math.harvard.edu/~hpasten/preprints/SqfPrimIJNT.pdf) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/4755) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/4765) · [Companion PR](https://github.com/google-deepmind/formal-conjectures/pull/4770) · [OMA](https://github.com/lefttosolve2/open-math-agents/issues?q=Cunningham) · [LTS](https://lefttosolve.com/api/solved)

Use the notebook's focused replay with `CunninghamSquarefreeWaitingTime`. The named axiom reports use only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the derivation and formalization. [Replay instructions](../../README.md#replay)
