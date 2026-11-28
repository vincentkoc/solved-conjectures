# Congruence tests for Hosoya values at power indices

Write $U(n)=F_n+L_{n+1}$ and fix $e\ge1$. For **every prime candidate $q$**, there is a prime $p$ with $U(p^e)=q$ if and only if every positive modulus admits a prime $p$ with $U(p^e)\equiv q$, with one exception. The exception is $q=3$ when $e$ is odd. In particular congruence tests detect actual prime values at prime-square indices exactly. One may omit every testing modulus divisible by a prime from any prescribed finite set. The witnessing prime can change with the modulus. [Prime-parameter theorem](HosoyaPrimePowerParameterClosure.lean) · [Earlier linear-index result](AlmostPrimeIndexClosure.md)

## Ordinary power indices

Let $U_{\mathbb Z}$ be the bilateral extension of $U$ by the Fibonacci recurrence. Fix an offset $r\ge0$ and a step $d\ge1$. An integer $y$ passes all congruence tests at the indices $r+dn^e$, with $n\ge0$, precisely when
$$
y=U_{\mathbb Z}(r+dv^e)\qquad\text{for some }v\in\mathbb Z .
$$
For **even $e$**, $v^e=|v|^e$, so every candidate surviving the tests occurs at a nonnegative parameter. For **odd $e$**, already at $r=0,d=1$ there are arbitrarily large positive candidates that pass every test and occur nowhere on the nonnegative upper diagonal. For example $U_{\mathbb Z}((-3)^3)=467861$ passes every cube-index test. The signed index is $-27$, and its positive value lies on the lower diagonal. The two nonnegative diagonals intersect only at 5. These extra values have no asserted primality. [Parity and unbounded examples](HosoyaPowerIndexClosure.lean) · [Diagonal intersection](LucasFibonacciDiagonalUnion.lean)

## A single modulus for the power test

For $w\ne0$, an integer congruence $t^e\equiv w\bmod 4w^2$ gives $t^e=w(1+4wc)$ for an integer $c$. The two factors are coprime, so each is an $e$th power up to sign. For odd $e$ one can absorb either sign. For even $e$ the second factor is 1 modulo 4 and therefore cannot be the negative of a square. It is positive, forcing $w\ge0$. Thus $w$ is an actual integer $e$th power. For $|w|\le B$, the modulus $4(B!)^2$ suffices for every nonzero $w$ and every positive exponent. Zero is itself an $e$th power. [Integer power test](HosoyaIntegerPowerTests.lean)

The earlier progression detector at a multiple of $4(B!)^2$ associates a signed parameter $w$ to any successful modular hit, with $|w|\le B=|y|+r+2$, $U_{\mathbb Z}(r+dw)=y$, and $w\equiv n^e\bmod 4(B!)^2$. In the reverse direction, approximate a signed base $v$ modulo a return period and raise to the $e$th power. The value moduli can still be chosen coprime to the prescribed primes, including primes dividing the parameter modulus. When $e$ is odd, large negative odd powers give positive lower values of unbounded size. [Bounded parameter recovery](HosoyaBoundedParameterRecovery.lean) · [Coprime detectors](CoprimeProgressionTests.md)

## Bases with a prescribed factor count

If $n$ must have exactly $k$ prime factors counted with multiplicity, the limits obtainable at **arbitrarily large bases for each testing modulus** are precisely
$$
U_{\mathbb Z}(r+dv^e),\qquad v\ne0,\quad \Omega(|v|)<k.
$$
Ordinary tests accept these limits and the values at fixed bases with exactly $k$ factors. The strict inequality follows from applying the previous factor-count detector to $n^e$, which has $ek$ factors, then recovering $w=v^e$. To see sufficiency, approximate $v$ by arbitrarily large bases with exactly $k$ factors in each needed residue class. For prime bases $k=1$, only $v=1,-1$ remain. At $r=0,d=1$ these give $U(1)=4$ and, only for odd $e$, $U_{\mathbb Z}(-1)=3$. No nonnegative upper value equals 3. [Factor-count classification](HosoyaPrimePowerParameterClosure.lean) · [Exact and cofinal tests](LucasFibonacciAlmostPrimeClosure.lean)

## Scope and checks

DeepMind’s pinned declaration asks for infinitely many distinct primes occurring as $U(n)$ at unrestricted nonnegative indices. The results here decide which individual candidates pass all power-index congruence tests. Existence of infinitely many prime values remains open. [Pinned declaration and sequence](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Ching et al.](https://arxiv.org/abs/2211.10788)

An independent calculation exhausted the residues modulo $4w^2$ in 960 tests with $1\le |w|\le40$ and $1\le e\le12$. For 1,788 pairs of exponent and modulus, 33,972 independent fast-doubling evaluations at signed power indices agreed with reduction through the full period. Modulo 3, the period is eight and the square-index values are 1 and 2.

Lean 4.33.1 rebuilt all 17 notebook modules in the dependency closure and independently replayed each with the kernel checker. The 61 named axiom reports use only `propext`, `Classical.choice` and `Quot.sound`. The notebook index check and five repository tests passed. The pinned sequence and prime-values question match their live upstream blob. Searches of DeepMind and Open Math Agents issues and pull requests and 11,460 Left to Solve records found the canonical statement and its formulation PR. No matching formalization of the power-index results appeared. Codex assisted with the proof. [Notebook replay](../../README.md#replay) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/8156) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents) · [Left to Solve](https://lefttosolve.com/api/solved)
