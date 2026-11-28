# Fixed Hosoya targets at prime parameters

Fix a prime $p$, an integer $y$, an offset $r\ge0$ and a step $d>0$. For $U_n=F_n+L_{n+1}$, one finite calculation decides whether every congruence $U_{r+dq}\equiv y\bmod p^h$ has arbitrarily large prime parameters $q$. The same calculation gives the exact normalized logarithmic prime mass at every sufficiently high level. It applies also at $p=2,5,11$ and when $p\mid d$. [Finite test and class count](HosoyaStableTargetClasses.lean) · [Prime mass](HosoyaFixedTargetPrimeMass.lean)

## The finite test

Write $X_n=2U_{n+1}-U_n$ and $\nu_p$ for the valuation of a nonzero integer. Set
$$
K=\max\{2,1+\nu_p(5y^2+44),1+\nu_p(5y^2-44)\}.
$$
Both discriminants are nonzero for integer $y$, since neither is divisible by 5. Let $T$ be the first positive return of $(F_n,F_{n+1})$ to $(0,1)$ modulo $p^K$. Put $P=4pT$, $j=2dpT$ and $a=\nu_p(F_j)$. For each $0\le i<P$ coprime to $P$, compute $v_i=\nu_p(X_{r+di})$. Keep $i$ just when $U_{r+di}\equiv y\bmod p^{a+v_i}$. The answer is the integer $C=\sum_{i\ {\rm kept}}p^{v_i}$. [Return period](HosoyaTargetLiftIsometry.lean) · [Representative test](HosoyaTargetLiftThreshold.lean)

For every $b\ge0$, take $h=a+K+b$ and $M=Pp^{K+b}$. Exactly $C$ reduced parameter residues modulo $M$ satisfy the target modulo $p^h$. Consequently
$$
\lim_{s\downarrow1}(s-1)
  \sum_{\substack{q\ {\rm prime}\\U_{r+dq}\equiv y\bmod p^h}}
  \frac{\log q}{q^s}
  =\frac{C}{\varphi(P)p^{K+b}}.
$$
If $C>0$, every level admits arbitrarily large prime parameters. If $C=0$, at all levels $h\ge a+K$ every prime hit divides $P$. In this case every level has a prime witness exactly when one of the prime divisors $q$ of $P$ satisfies the integer equality $U_{r+dq}=y$. This checks the isolated witnesses as well as the cofinal ones. The fixed-target mass therefore either vanishes or falls by exactly a factor of $p$ at each higher level. When the target varies with the level the earlier square-root bound is sharp at 13. [Count and infinitude equivalence](HosoyaStableTargetClasses.lean) · [Exact limit](HosoyaFixedTargetPrimeMass.lean) · [Uniform bound and moving targets](PrimePowerIndexConcentration.md)

## Why the count stabilizes

At a hit modulo $p^K$ the Pell identity $X_n^2=5U_n^2+44(-1)^n$ gives $2\nu_p(X_n)=\nu_p(5y^2+44(-1)^n)<K$. Translating by multiples of $T$ fixes the companion modulo $p^K$, so its valuation is constant on the midpoints used in each phase. The difference identity
$$
U_{n+2t}-(-1)^tU_n=F_t X_{n+t}
$$
then gives an exact congruence test. On a successful phase $q=i+Pu$, two values agree modulo $p^{a+v_i+e}$ exactly when their parameters $u$ agree modulo $p^e$. Dividing the differences from the phase representative by $p^{a+v_i}$ induces an injection on the finite ring of residues modulo $p^e$, hence a bijection. Exactly one $u$-class survives at exponent $e=K-v_i+b$. This accounts for $p^{v_i}$ classes modulo $M$. A failed representative cannot acquire a later hit. Dirichlet's theorem supplies large primes in each reduced class, and the logarithmic prime mass of each such class is $1/\varphi(M)$. [Midpoint identity and finite bijection](HosoyaTargetLiftIsometry.lean) · [Phase classification](HosoyaTargetLiftThreshold.lean) · [Reduced-class mass](HosoyaReducedClassMass.lean)

For $r=0,d=1,p=2,y=23$, the test gives $(K,a,P,C)=(2,5,48,1)$ and mass $1/(64\cdot2^b)$ at $h=7+b$. At $p=2,y=4$ the surviving companion has valuation one, giving $(3,6,96,2)$. At $p=11,y=23$ the count is zero even though $U_5=23$ and 5 is prime. Here 5 divides the phase period. These examples are independent arithmetic checks. Across twelve choices of $(p,r,d,y)$, a direct recurrence enumerated 17,055,412 phase entries at 32 levels using $p=2,3,5,7,11,13$.

## Scope and sources

The pinned DeepMind declaration asks whether infinitely many distinct prime **values** occur at arbitrary natural indices. Here primality concerns the parameter $q$ and the event concerns a congruence on the value. Infinitude of prime values remains open. The primary paper studies primes in the determinant Hosoya triangle. Carlip and Somer treat frequencies of second-order recurrences modulo prime powers. This notebook records a Lean formalization of the fixed-target count with a prime parameter. [Pinned declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Ching, Flórez, Luca, Mukherjee and Saunders](https://arxiv.org/abs/2211.10788) · [Carlip and Somer](https://dml.cz/handle/10338.dmlcz/134189)

Searches of DeepMind and Open Math Agents issues and pull requests, and 11,904 Left to Solve records, returned the DeepMind statement and its issue. No matching formalization of this fixed-target count appeared. The clean Lean 4.33.1 replay covered 29 notebook modules. The 99 named axiom reports use only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the proof. For a focused replay, use the notebook runner with the module `HosoyaFixedTargetPrimeMass`. [Replay instructions](../../README.md#replay) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/8156) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents) · [Left to Solve](https://lefttosolve.com/api/solved)
