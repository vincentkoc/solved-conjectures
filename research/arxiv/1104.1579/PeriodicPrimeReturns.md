# Periodic confinement of Cunningham prime returns

Fix any positive integer $M$ and either Cunningham recurrence. Infinitely many prime seeds $p$ have the property that if the term at index $j$ is prime, then $M\mid j$. The same seed satisfies the restriction at every future index. The prime at index zero is included. The result leaves open whether there is any later prime on these particular orbits. [Lean theorem](CunninghamPeriodicReturnCover.lean) · [Pinned recurrences](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean)

More precisely, there are positive integers $D,W$ with $M\mid D$. For each kind there is a reduced seed class $A\bmod W$ such that every positive seed $p$ in that class satisfies
\[
  \gcd(T_j(p),W)=1 \quad\Longleftrightarrow\quad D\mid j.
\]
Thus the two kinds have the same local period, though the two seed classes may differ. Dirichlet supplies arbitrarily large primes in each class. Once $p>W$, a term sharing a prime factor with $W$ is composite because $T_j(p)\ge p$. Jones asks for infinitely many seeds with a prime at **every** site below a given length and a composite at the next site. Both exact-length conjectures remain open. [Seed classes and infinitude](CunninghamPeriodicReturnCover.lean) · [Jones](https://arxiv.org/abs/1104.1579)

## How the covering primes are chosen

Write $M=2^L m$ with $m$ odd. A prime divisor of the Fermat number $2^{2^i}+1$ detects the exponents $j$ for which $v_2(j)=i$, by the congruence $2^j\equiv-1$. The first $B$ such primes leave exactly the multiples of $2^B$. This gives the whole construction when $m=1$. [Fermat cover](CunninghamReturnCoverPrimes.lean)

For $m>1$, use prime divisors of the cyclotomic values $\Phi_m(-2^{2^a})$. As $a$ grows, only finitely many of these values are $0$ or $\pm1$, because a nonconstant polynomial has finite fibers. A prime divisor $q$ also divides $(2^m)^{2^a}+1$, so for large $a$ it satisfies $q>2^a\ge m$. The cyclotomic root modulo $q$ therefore has exact order $m$. If $B>a$, squaring removes the minus sign and preserves that odd order, giving $\operatorname{ord}_q(2^{2^B})=m$. Distinct depths give distinct primes. These primes also differ from every Fermat divisor used at depth below $B$, where $2^{2^B}$ has order one. [Cyclotomic and simultaneous-order lemmas](CunninghamReturnCoverPrimes.lean)

Choose $m-1$ such primes with a common $B\ge L$. At the prime assigned to $r=1,\ldots,m-1$, make the term vanish at $j=2^B r$. On the remaining exponents $j=2^B k$ this covers exactly $k\equiv r\pmod m$. None of the forbidden classes contains zero, so the corresponding seed residue at every covering prime is nonzero. The Chinese remainder theorem combines them into a reduced class, leaving precisely $D=2^B m$ as the period of the terms coprime to their product. Finite covering congruences and primitive prime divisors also appear in the Sierpiński–Riesel literature. [Construction](CunninghamPeriodicReturnCover.lean) · [Bispels et al., §2](https://math.colgate.edu/~integers/aa12/aa12.pdf)

## A period of 24

Use the primes $3,5,17,13,241$ at sites $1,2,4,8,16$, respectively. Their product is 798915. The first-kind seed 5856073 and second-kind seed 6926567 are both prime. For each seed, its term at index $j$ is coprime to the product exactly when $24\mid j$. Independent modular calculations also checked periods 32 and 80 for both kinds over every residue of each period. The exact local period can exceed the originally requested divisor $M$. [General proof](CunninghamPeriodicReturnCover.lean)

The main declarations are `CunninghamChain.ReturnCover.periodic_seed_classes` and `CunninghamChain.ReturnCover.infinitely_many_confined_prime_returns`. Lean 4.33.1 rebuilt all ten notebook modules from fresh output. Each passed an independent kernel replay, and all 36 named axiom reports used only `propext`, `Classical.choice` and `Quot.sound`. Live searches of DeepMind and Open Math Agents issues and pull requests and 6,518 Left to Solve records found the canonical integer-chain question and related reductions, with no matching periodic-cover formalization. Codex assisted with the Lean proof. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/4755) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/4765) · [OMA search](https://github.com/lefttosolve2/open-math-agents/issues?q=Cunningham) · [LTS records](https://lefttosolve.com/api/solved) · [Notebook replay](../../README.md#replay)
