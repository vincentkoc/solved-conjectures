# How many primes can cover a Cunningham orbit?

For either Cunningham recurrence and every prime seed $p$, **no seven primes divide all its positive-index terms**. If $S$ contains at most seven odd primes, every block of $2^{|S|}$ consecutive indices contains a term divisible by none of them. This includes blocks starting at zero. Divisibility here allows a term to equal its covering prime. An escaping term may still be composite. [Lower bound and certificate](CunninghamSevenPrimeCover.lean)

More generally, write $U_b(p,j)$ for the $j$-th term under $x\mapsto 2x+1$ or $x\mapsto 2x-1$. Given a size bound $k$, let $D=2^{\max(k-1,0)}$ and take the prime divisors of

$$
P_D=\prod_{d=1}^{D}(2^d-1).
$$

There is a cover of all positive sites by at most $k$ primes if and only if there is a subset of at most $k$ odd candidate primes which contains $p$ and covers the first $2^k$ positive sites. This is a finite test for both signs, uniformly in $p$. [Finite criterion](CunninghamFiniteCoverSearch.lean)

## Why the seed has to occur in the cover

An odd prime $q$ either divides no term or divides precisely the terms in one residue class modulo the multiplicative order of 2 modulo $q$. A family of $k$ such classes that leaves even one index uncovered leaves an uncovered site in every block of $2^k$. This is the classical Crittenden–Vanden Eynden theorem. The proof here represents each class by a root-of-unity equation. Multiplying their differences gives a sum of $2^k$ geometric sequences. A finite-difference induction shows that if this sum vanishes for that many consecutive indices, it vanishes everywhere. [Local divisibility classes](CunninghamSquarefreeLocalFactors.lean) · [Geometric sequences](CunninghamGeometricWindow.lean) · [Balister, Bollobás, Morris, Sahasrabudhe and Tiba](https://par.nsf.gov/servlets/purl/10165575) · [Existing Erdős 275 formalization](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos275.lean)

Every positive-index term at a prime seed is odd, so 2 can be removed from a cover. A cover of every positive index must also divide the term at index zero, which equals $p$. Thus the cover contains $p$. Now remove an indispensable prime $q$ from a minimal cover of size $m$. At each site escaping the other $m-1$ primes, $q$ must divide the term. Two such sites can be chosen at a positive distance of at most $2^{m-1}$. Their difference is a multiple of the order of 2 modulo $q$, which puts $q$ among the divisors of $P_D$. The general modulus bound also occurs in the classical covering literature. [Orbit and order proof](CunninghamOrbitCoverWindow.lean) · [Classical interval and modulus bounds](https://par.nsf.gov/servlets/purl/10165575)

## The seven-prime certificate

At $k=7$ there are 95 primes in the candidate list. Lean checks a Lucas primality witness for each entry and verifies that $P_{64}$ divides the 64th power of their product $B$. This certifies that the list contains every possible covering prime. For each listed seed the certificate gives two positive indices, one per recurrence, at which the corresponding term is coprime to $B$. The largest listed first-kind escape is at 65 and the largest second-kind escape is at 63. A separate integer calculation factored all 64 Mersenne numbers and found the first escaping site directly for each seed and sign. [Certificate and witnesses](CunninghamSevenPrimeCover.lean)

## Frequency among prime seeds

Let $C(X,k)$ count primes at most $X$ having a cover of size at most $k$ on **either** recurrence, counted once. The product of the distinct covering candidates divides $P_D$. Bounding each Mersenne factor by $2^D$ gives a total candidate weight of at most $4^k\log 2$, where each candidate prime $q$ has weight $\log q$. Splitting the seed set at $\sqrt X$ gives the explicit inequality

$$
 C(X,k)\log X \le 2\cdot 4^k\log 2 + \sqrt X\log X
 \qquad(X\ge 2).
$$

Consequently, if $4^{k(X)}/X\to0$, then $C(X,k(X))/\pi(X)\to0$. For instance, the conclusion holds when $k(X)$ lies below one half of $\log_2 X$ by a quantity tending to infinity. A prime outside this exceptional set requires more than $k(X)$ divisors for a cover under either sign. [Prime-relative density theorem](CunninghamCoverSeedDensity.lean)

## Scope and sources

The pinned Jones declarations ask for infinitely many prime prefixes of each exact positive length. Here the prime seed is fixed and the infinite forward orbit is tested for divisibility by a finite set. These theorems leave both Jones infinitude questions open. The quantifier on the prime seed matters. Classical Sierpiński and Riesel covers use other coefficients in the exponential progression. [Pinned canonical recurrences and questions](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean) · [Jones](https://arxiv.org/abs/1104.1579) · [Cowles and Gamboa on formal prime covers](https://www.cs.uwyo.edu/~ruben/static/pdf/sierpinski.pdf)

Live duplicate checks covered the Jones issue and both formulation PRs, OMA issues and PRs, and 11,071 LTS solved records. They identified two existing DeepMind PRs for the classical interval theorem and three LTS subgoals on exact Jones chains. The specialized prime-seed test, the seven-prime exclusion and its seed-counting bound were not found in those records. Codex assisted with the proof. [Jones issue](https://github.com/google-deepmind/formal-conjectures/issues/4755) · [Generic interval proof PR](https://github.com/google-deepmind/formal-conjectures/pull/3283) · [Earlier interval proof PR](https://github.com/google-deepmind/formal-conjectures/pull/2762) · [OMA search](https://github.com/lefttosolve2/open-math-agents/issues?q=Cunningham) · [LTS records](https://lefttosolve.com/api/solved)

Lean 4.33.1 rebuilt and independently kernel-replayed 14 notebook modules, including the numerical certificate. All 43 named axiom reports stayed within `propext`, `Classical.choice` and `Quot.sound`. The working cache and the cited pin have identical Jones source, imported upstream modules, toolchain and Lake dependency manifest. [Replay instructions](../../README.md#replay)
