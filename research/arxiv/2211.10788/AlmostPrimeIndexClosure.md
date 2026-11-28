# Congruence tests at prime and almost-prime Hosoya indices

**The only prime that passes every prime-index congruence test without occurring at a prime index is 3.** Write $U(n)=F_n+L_{n+1}$. For every prime $q\ne3$, the following are equivalent.

1. For each positive modulus $M$, some prime $p$ satisfies $U(p)\equiv q\pmod M$.
2. Some prime $p$ satisfies $U(p)=q$.

Requiring $p$ to be arbitrarily large at each modulus changes the conclusion. The only integer candidates that then survive are 3 and 4, from the signed indices $-1$ and $1$. The prime 5 is an actual value at prime index 2, but it fails the unbounded-index test already modulo 4. The prime 31 passes the unrestricted-index test for every modulus. At prime indices it fails modulo 58. The only possible index residues are 21 and 35 modulo 42, and neither contains a prime. [Prime-index declarations and certificate](LucasFibonacciPrimeIndexClosure.lean) · [Earlier unrestricted tests](UpperCongruenceClosure.md)

## The parameter with fewer factors

Extend the upper sequence to $U(z)=2F_z+F_{z+2}$ for all integer indices. Fix an offset $r\ge0$, step $d>0$, and integer $k\ge0$. Let a parameter $t>0$ have exactly $k$ prime factors counted with multiplicity, so $k=1$ means prime and $k=0$ means $t=1$. For each fixed integer candidate $y$, modular hits $U(r+dt)\equiv y\pmod M$ exist at **arbitrarily large** such parameters for every $M>0$ if and only if there is an integer $w\ne0$ with

$$
U(r+dw)=y,\qquad \Omega(|w|)<k.
$$

Without the arbitrarily-large requirement, one must also include the actual values at positive parameters having exactly $k$ factors. Both statements remain true if all testing moduli divisible by any prime factor of a fixed positive integer $E$ are discarded. There is a finite witness search since every possible $w$ has $|w|\le |y|+r+2$. The special case $k=1$ leaves at most the limits $U(r+d)$ and $U(r-d)$. [General classification](LucasFibonacciAlmostPrimeClosure.lean) · [Index bound and modular recovery](HosoyaBoundedParameterRecovery.lean)

To see why the strict inequality appears, set $B=|y|+r+2$ and take $D=2^{k+1}B!$. The earlier progression detectors yield a modulus coprime to $E$ for which a successful parameter $t$ recovers a signed witness $w\equiv t\pmod D$. The factor $2^{k+1}$ excludes $w=0$. Every nonzero $|w|\le B$ divides $D$, hence divides $t$. Once $t>B$, this divisor is proper and uses strictly fewer factors than $t$. One can include any prescribed $H$ in $D$ to force $t\equiv w\pmod H$ at the same time. [Almost-prime parameter arithmetic](HosoyaAlmostPrimeParameters.lean) · [Coprime progression detectors](CoprimeProgressionTests.md)

Conversely, let $P$ be a period of the recurrence modulo the test modulus. Multiply $|w|$ by primes congruent to 1 modulo $P$ and one last prime in the class of the sign of $w$. Dirichlet’s theorem makes that last prime as large as required. The resulting number has exactly $k$ factors, lies in the class of $w$, and produces the required value modulo the test modulus. A finite set of small parameters can be excluded by enlarging the test modulus while keeping it coprime to $E$, unless one of them already yields $y$ exactly. [Signed recurrence](LucasFibonacciCongruenceClosure.lean) · [General classification](LucasFibonacciAlmostPrimeClosure.lean)

## Prime mass of the tests

At either of the two limit values, each individual modulus accepts a reduced prime progression and gives an eventually positive lower bound for normalized logarithmic Dirichlet mass. For every candidate, including these two, and every $\varepsilon>0$, there is also a single allowed modulus whose accepted prime parameters have normalized mass below $\varepsilon$ for all $s>1$ sufficiently close to 1. The normalization is $(s-1)\sum_{p\text{ accepted}}\log(p)/p^s$. A testing modulus that confines large parameters modulo a large prime $H$ leaves only the two residues $1$ and $-1$ there. [Mass bounds](HosoyaPrimeIndexTestMass.lean)

## Scope and checks

The upstream declaration concerns infinitely many distinct prime values at **arbitrary nonnegative** indices. This classification tests individual candidates at prime or almost-prime parameters and leaves the upstream infinitude question open. The earlier formal progression theorem handles all parameters in one arithmetic progression. General rank-one local–global results for exponential polynomials and work on Skolem zeros at prime-power indices supply related context. [Pinned definition and question](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Earlier progression theorem](IndexProgressionClosure.md) · [Bartolome, Bilu and Luca](https://doi.org/10.4064/aa159-2-1) · [On the Skolem Problem and Prime Powers](https://arxiv.org/abs/2006.07432) · [Ching et al.](https://arxiv.org/abs/2211.10788)

An independent recurrence calculation enumerated 2,970 periods across three progressions, factor counts 1, 2, 3, and moduli 1 through 330. All 191 integer candidates from −40 through 150 agreed with the bilateral classification for both ordinary and unbounded-parameter tests on each progression and factor count. When the prime factors of 2310 were excluded from the testing moduli, 71 still separated 31 at prime indices and 19 separated 5 at unbounded prime indices. [Replay instructions](../../README.md#replay)

Lean 4.33.1 independently replayed 17 notebook modules. All 62 named axiom reports use only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. The pinned upstream file matches the live source blob. The two canonical DeepMind issues, OMA issues and pull requests, and 10,978 LTS solved records were checked for related formalizations. Codex assisted with the proof. [Upper-sum issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [Related issue](https://github.com/google-deepmind/formal-conjectures/issues/8156) · [OMA search](https://github.com/lefttosolve2/open-math-agents/issues?q=Hosoya) · [LTS records](https://lefttosolve.com/api/solved)
