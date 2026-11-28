# Joint Hosoya values at prime parameters

Let $U_n=2F_n+F_{n+2}$. Fix a testing prime $p$ and two distinct affine index maps $r+dt$ and $s+ft$, with $d,f>0$. At a prime parameter $t$, prescribe the residues of **both** values modulo $p^h$. The normalized logarithmic prime mass of this event has a uniform upper bound of order $p^{-h}$. The exponent is sharp even for the fixed pair of targets $(U_{r+d},U_{s+f})$. The offset, slope and testing prime may affect the constants. The question of infinitely many primes among the $U_n$ remains open. [Upper bound](HosoyaJointPrimeMass.lean) · [Sharp lower bound](HosoyaSharpJointPrimeMass.lean) · [Pinned DeepMind question](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean)

For a set $A$ of prime parameters write $D(A,x)=(x-1)\sum_{t\in A}(\log t)/t^x$ for $x>1$. Let $A_h(y,z)$ consist of the prime parameters satisfying both target congruences. There are $H\ge0$ and $C>0$ such that for each $b\ge0$ and $\varepsilon>0$, throughout a right neighborhood of 1,
$$
 D(A_{H+b}(y,z),x)<C/p^b+\varepsilon \qquad\text{for all integer targets }y,z.
$$
Conversely, there is $c_p>0$ such that, for every pair of index maps and each $b\ge0$, throughout a right neighborhood of 1,
$$
 c_p/p^b \le D(A_b(U_{r+d},U_{s+f}),x).
$$
At $p=13$ the maps $t$ and $1+t$ each fail the individual full-rate bound. They have critical parameter residues 23 and 113 modulo 182, respectively. Their joint values obey the bound above. Repeating a single index map would preserve its large fibres when the two targets coincide. [Individual criterion](UniformPrimeFibreCriterion.md) · [Neighboring example](HosoyaSharpJointPrimeMass.lean)

## Why the second value helps

Put $X_n=2U_{n+1}-U_n$, with $X_0=7$ and $X_1=6$. For distinct affine index maps, every pointwise gcd of $X_{r+dt}$ and $X_{s+ft}$ divides one fixed positive integer. For unequal slopes, let $w^2=w+1$ and suppose $d<f$. In the quadratic algebra modulo a common divisor, $w^n=F_{n+1}(7w-6)$ at each companion zero. Raising to the two slopes and cancelling the common power eliminates $t$. The divisor then divides the coefficient of $w$ in
$$
 (w-1)^{fr}w^{ds}(7w-6)^{f-d}.
$$
This coefficient is nonzero. At the two roots $4,-3$ of $w^2-w-1$ modulo 11, the expression vanishes at just the first. At equal slopes and distinct offsets the determinant of the value and companion coordinates gives the bound $22F_{|s-r|}$. The earlier pointwise gcd theorem concerns the values $U_n$ themselves. [Companion gcd](HosoyaAffineCompanionBounds.lean) · [Value gcd](LucasFibonacciAffineGCD.lean)

Choose $K$ so that $p^K$ exceeds the companion gcd bound and choose an even return $E$ divisible by $p$ with $p^K\mid F_E$. At each phase $i$ modulo $2E$, at least one companion is regular, meaning its valuation is less than $K$. On this phase, the difference formula $U_{n+2j}-U_n=F_j X_{n+j}$ for even $j$ recovers $b$ more base-$p$ digits of the parameter from equality of both values to a fixed extra precision. This holds for all natural parameters. Among prime parameters it gives a cover by at most $2E$ reduced residue classes modulo $2Ep^b$, apart from finitely many small primes. Dirichlet’s theorem in its logarithmic-mass form gives the upper bound. For the lower bound a progression $t\equiv 1\bmod 2E'p^b$, with $E'$ depending only on $p$, preserves both parameter-one targets modulo $p^b$. [Recovery theorem](HosoyaJointParameterRecovery.lean) · [Midpoint formula](HosoyaTargetLiftIsometry.lean) · [Prime progression mass](../1104.1579/CunninghamPrimeDirichletMass.lean)

Ching and coauthors study the primes of the determinant Hosoya triangle. Carlip and Somer analyze frequencies of individual recurrence residues modulo prime powers. Moree and Stevenhagen study prime divisors of the Lagarias sequence, which begins one index before $U$. The theorem here concerns joint congruences at a common prime parameter. [Ching et al.](https://arxiv.org/abs/2211.10788) · [Carlip and Somer](https://dml.cz/handle/10338.dmlcz/134189) · [Moree and Stevenhagen](https://www.numdam.org/item/JTNB_2001__13_1_241_0/)

Independent integer checks covered 15,300 companion gcds for 300 distinct pairs of index maps, 236,208 comparisons within regular phases, and 1,920 simultaneous returns to the fixed targets. Codex assisted with formalization.

Live searches of the DeepMind and Open Math Agents issues and PRs and 12,405 Left to Solve records found the canonical statement and its issue. No matching joint affine result appeared. The pinned and live sequence files had the same Git blob. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/8156) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents) · [Left to Solve](https://lefttosolve.com/api/solved)

A fresh Lean 4.33.1 build and independent kernel replay checked 33 notebook modules. All 107 named axiom reports used only `propext`, `Classical.choice` and `Quot.sound`. The five named theorems in the four new modules each have an axiom report. Run the focused notebook replay with `HosoyaSharpJointPrimeMass`. [Replay instructions](../../README.md#replay)
