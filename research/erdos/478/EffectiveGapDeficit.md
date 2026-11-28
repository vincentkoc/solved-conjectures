# An effective factorial-deficit subsequence

Write $A_p=\{j!\bmod p:1\le j<p\}$ and $\delta_p=p-|A_p|$. For every integer $n\ge2$ there is a prime
$$
n<p\le 2^{(n+2)^{3n+8}}
$$
at which the polynomial $f_n(X)=X(X-1)\cdots(X-n+1)-1$ splits into $n$ distinct linear factors. Its $n$ roots provide distinct upper endpoints of factorial collisions. Hence $|A_p|+n\le p-1$ and $\delta_p\ge n+1$. Both the prime bound and the collision count hold for the same prime. [Lean declarations](Erdos478EffectiveGapDeficit.lean) · [Endpoint argument](Erdos478UnboundedDeficit.lean)

For every real $\varepsilon>0$, arbitrarily large primes satisfy
$$
\delta_p\ \ge\ \frac{\log\log p}{(3+\varepsilon)\log\log\log p}.
$$
The declaration `Erdos478.EffectiveResolvent.frequently_logarithmic_deficit` also proves $\log\log\log p\ge1$ on these witnesses. In particular, $\limsup_{p\to\infty}\delta_p\log\log\log p/\log\log p\ge1/3$ along primes. Banks, Luca, Shparlinski and Stichtenoth proved the stronger constant $1$ using effective Chebotarev. Their count allows $j\ge p$, which represents the additional class zero. The difference of one does not affect the asymptotic constant. Klurman and Munsch proved quantitative average results. Here an elementary integer polynomial argument gives a Lean proof of the displayed rate and an explicit witness bound for each gap length. [Banks et al., Theorem 3](https://mospace.umsystem.edu/server/api/core/bitstreams/5b756a2f-14b6-4cd7-b23e-f57366effec4/content) · [Klurman and Munsch](https://www.numdam.org/item/10.5802/jtnb.974.pdf)

## A polynomial detecting complete splitting

Let $f$ be a monic separable integer polynomial of degree $n>0$, with complex roots $a_0,\ldots,a_{n-1}$. Choose an integer $0\le M\le n(n!)^2$ so that all $n!$ sums $u_\sigma=\sum_{i<n}M^i a_{\sigma(i)}$ are distinct. For two different permutations the difference is a nonzero polynomial in $M$ of degree less than $n$. Their product has degree at most $n(n!)^2$, so the indicated interval contains a suitable integer. The permutation resolvent is
$$
R(T)=\prod_{\sigma\in S_n}(T-u_\sigma).
$$
Its coefficients are symmetric polynomials with integral coefficients in the $a_i$. Expressing them in the elementary symmetric functions gives an integer polynomial with the same product formula in every characteristic. [Bounded separating parameter](Erdos478ResolventSeparator.lean) · [Integral resolvent and specialization](Erdos478PermutationResolvent.lean)

At a prime where both $f$ and $R$ are separable, a root of $R$ in $\mathbb F_p$ forces $f$ to split completely there. Frobenius permutes the roots of $f$ and fixes the chosen sum. The sums remain distinct, so the permutation fixes the entire ordered tuple. Each root of $f$ then lies in the prime field. [Frobenius proof](Erdos478ResolventFrobenius.lean)

## Bounding the witness prime

For a monic polynomial $g$ with distinct roots of norm at most $U\ge1$, the absolute resultant of $g$ and $g'$ is positive and at most $(2U)^{(\deg g)^2}$. Let $B$ be the product of these absolute resultants for $f$ and $R$. Take $U$ large enough for all roots of $R$, put $t=U+2$ and $c=R(t)$, and evaluate $R$ at $w=t+(2U+1)Bc^2$. The integer quotient $R(w)/c$ has absolute value greater than one and is congruent to one modulo $B$. Any prime dividing it avoids $B$ and gives a root of $R$ modulo that prime. Bounding the polynomial values gives the explicit ceiling in `bounded_splitting_prime`. [Resultant and root bounds](Erdos478ResolventHeight.lean) · [Bounded Schur prime](Erdos478BoundedSchurPrime.lean) · [Splitting-prime theorem](Erdos478EffectiveSplitting.lean)

Every complex root of $f_n$ has norm at most $n+1$, since outside that disk all $n$ factors have norm greater than one. The logarithm of the witness bound is at most cubic in $n!$, times a polynomial in $n+2$. Using $n!\le n^n$ gives the displayed double-exponential bound. Taking logarithms twice gives $\log\log p\le(3n+8)\log(n+2)$. If $n+2\le\log\log p$, replace $\log(n+2)$ by $\log\log\log p$. In the other case the direct bound $\delta_p\ge n+1$ suffices for large $n$. [Size estimate](Erdos478ResolventScale.lean) · [Logarithmic deficit](Erdos478EffectiveGapDeficit.lean)

For example, at $n=4$ the prime 23 gives roots $4,8,18,22$ and misses seven residue classes. At $n=5$ the prime 1931 gives roots $33,77,924,1030,1808$ and misses 701. Direct enumeration uses the same factorial interval as the theorem.

## Scope and replay

The pinned question asks whether $|A_p|/p$ tends to $1-1/e$ along all primes. The explicit splitting and deficit results concern a subsequence. The earlier density-one theorem gives each fixed deficit threshold on almost all primes. The earlier finite gap sieve bounds the frequency of specified gap lengths. The present bound makes the deficit grow as an explicit function of each witness prime. [Pinned Erdős 478](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean) · [Density-one theorem](FactorialDeficitDensity.md) · [Finite gap sieve](PrimeGapSieve.md)

The 2026-11-28 overlap check found the DeepMind statement issue and statement PR, the open Left to Solve target, and separate OMA proofs about a factorial sum and a divisor count. The elementary proof uses mathlib's fundamental theorem of symmetric polynomials, Vieta's formulas and finite-field Frobenius. The only earlier notebook imports in its closure provide gap irreducibility and the count of repeated endpoints. [Statement issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5229) · [Left to Solve](https://lefttosolve.com/p/Erdos478.erdos_478) · [OMA factorial sum](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4056) · [OMA divisor count](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7450)

The notebook runner discovers the eight new Lean modules and their two earlier imports. The scoped replay rebuilds the ten modules in an empty directory with Lean 4.33.1, treats warnings as errors and runs the independent kernel checker. All 14 named declaration audits use only `propext`, `Classical.choice` and `Quot.sound`. [Notebook replay](../../README.md#replay)
