# Uniform prime-parameter fibres of the upper Hosoya sequence

Let $U_n=F_n+L_{n+1}$ and $X_n=2U_{n+1}-U_n$. Fix a prime $p$, an offset $r\ge0$ and a step $d>0$. A finite test decides whether the mass of prime parameters $q$ satisfying $U_{r+dq}\equiv y\bmod p^h$ is $O_{p,r,d}(p^{-h})$ uniformly in the integer target $y$. When the test finds a critical residue, some targets attain square-root order at arbitrarily high levels. The target is allowed to change with the level. [Criterion and mass bounds](HosoyaPrimeFibreCriterion.lean) · [Earlier square-root upper bound](PrimePowerIndexConcentration.md) · [Exact count for a fixed target](FixedTargetPrimePowerMass.md)

## The test

Choose $E$ as the least common multiple of $2$, $p$ and the least positive $t$ with $p^2\mid F_{dt}$. Compute $a=\nu_p(F_{dE})\ge2$. Search $0\le i<E$ with $\gcd(i,E)=1$ for a **critical residue** satisfying $p^a\mid X_{r+di}$. Any positive even $E$ divisible by $p$ with $\nu_p(F_{dE})\ge2$ gives the same yes-or-no decision. [Return and equivalence](HosoyaPrimeFibreCriterion.lean)

Write $D_h(y,s)=(s-1)\sum_q (\log q)/q^s$, with the sum restricted to the prime parameters satisfying the congruence at level $h$. If the search returns no critical residue, then for every $b\ge0$ and $\varepsilon>0$, simultaneously for all $y$ as $s$ approaches 1 from above,
$$
D_{2a+b}(y,s)<\frac{2E}{\varphi(2E)p^b}+\varepsilon.
$$
If the search returns a critical residue, for every $b$ there is an integer $y_b$ such that throughout a right neighborhood of 1,
$$
D_{2(a+b)}(y_b,s)\ge\frac{1}{4Ep^b}.
$$
These alternatives are incompatible with a common full-rate bound on the critical side. The earlier unconditional upper bound gives square-root order there. [Prime-fibre criterion](HosoyaPrimeFibreCriterion.lean) · [Uniform upper bound](HosoyaPrimePowerUniformMass.lean)

## Proof and examples

For even $j$, the difference $U_{n+2j}-U_n$ factors as $F_j X_{n+j}$. On a regular residue, divisibility by powers through $p^a$ is unchanged along returns. The companion valuation stays constant, so two parameters at the same target and phase must agree to $b$ further base-$p$ digits. The large prime hits are covered by at most $2E$ reduced classes modulo $2Ep^b$. At a critical residue, lifting the primitive companion recurrence gives a reduced class modulo $2Ep^b$ on which both factors of the difference gain $b$ digits. Every prime in this class hits the same target to precision $p^{2(a+b)}$. [Companion lifts](HosoyaCriticalCompanionLifts.lean) · [Midpoint identity](HosoyaTargetLiftIsometry.lean)

| Testing prime | Offset | Step | Return $E$ | Depth $a$ | Outcome |
| --- | --- | --- | --- | --- | --- |
| 7 | 0 | 1 | 56 | 2 | Full rate |
| 7 | 1 | 1 | 56 | 2 | Critical at 15 |
| 13 | 0 | 1 | 182 | 2 | Critical at 23 |
| 13 | 0 | 13 | 182 | 3 | Full rate |
| 17 | 0 | 1 | 306 | 2 | Critical at 185 |
| 23 | 0 | 1 | 552 | 2 | Critical at 473 |

More generally, if $-220(-1)^{r+d}$ is a nonsquare modulo $p$, the Pell identity rules out a critical residue. For $p=7,r=0,d=1$, the constant is $3\bmod 7$. The proofs of the examples use exact integers with fast Fibonacci doubling. [Nonsquare obstruction and examples](HosoyaPrimeFibreExamples.lean)

## Scope and verification

The pinned DeepMind conjecture asks whether infinitely many distinct prime **values** $U_n$ occur at arbitrary natural indices. Here the prime variable is $q$ in the affine index $r+dq$. The prime-values conjecture remains open. Ching and coauthors study primes of the determinant Hosoya triangle. Carlip and Somer study the distribution of second-order recurrences modulo prime powers. [Pinned declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Ching et al.](https://arxiv.org/abs/2211.10788) · [Carlip and Somer](https://dml.cz/handle/10338.dmlcz/134189)

A separate fast-doubling calculation checked 16,866 reduced residues in 90 prime, offset and step combinations. Fourteen combinations had a critical residue. It checked 294 equalities on lifted critical classes and 127,488 comparisons on regular classes. Live searches of DeepMind and Open Math Agents issues and PRs, and 12,097 Left to Solve records, found the original issue and formal statement. No matching prime-parameter criterion appeared. Codex assisted with the proof. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/8156) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents) · [Left to Solve](https://lefttosolve.com/api/solved)

A fresh Lean 4.33.1 build and independent kernel replay checked 29 notebook modules. All 102 named axiom reports used only `propext`, `Classical.choice` and `Quot.sound`. The 13 public theorems in the three new modules each have an axiom report. Run the focused notebook replay with `HosoyaPrimeFibreExamples`. [Replay instructions](../../README.md#replay)
