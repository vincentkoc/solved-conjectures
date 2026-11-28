# Prime-index Hosoya values modulo powers of one prime

Fix any prime $\ell$ and positive step $d$. For the upper sequence $U(n)=F_n+L_{n+1}$, consider the prime parameters $q$ satisfying
$$
U(r+dq)\equiv y\pmod{\ell^h}.
$$
As $h$ grows, their normalized logarithmic Dirichlet mass tends to zero **uniformly over the offset $r\ge 0$ and the integer target $y$**. More precisely, for each $\varepsilon>0$ a single $H$ and a single right neighborhood of $s=1$ suffice for every $h\ge H$, $r$ and $y$. This includes $\ell=2,5,11$. The earlier theorem allowed the testing modulus to depend on the candidate. [Uniform bound](HosoyaPrimePowerUniformMass.lean) · [Earlier congruence tests](AlmostPrimeIndexClosure.md)

For a set $A$ of accepted prime parameters the normalization is
$$
(s-1)\sum_{q\in A}\frac{\log q}{q^s}.
$$
There is an integer $a=a(\ell,d)$ such that at modulus $\ell^{2(a+b+1)}$ the mass is eventually less than $2/\varphi(\ell^b)+\varepsilon$, uniformly in $r,y$. Thus the decay in the testing modulus $M$ is of order at most $M^{-1/2}$, with a constant depending on the fixed prime and step, in the limiting upper mass as $s\downarrow1$. At a fixed parity all successful parameters, including composite ones, occupy at most two residue classes modulo $\ell^b$. [Two-class theorem](HosoyaPrimePowerIndexClasses.lean) · [Prime mass and quantifiers](HosoyaPrimePowerUniformMass.lean)

## Why only two classes survive

Set $X_n=2U(n+1)-U(n)$. Then $X_n^2=5U(n)^2+44(-1)^n$. Two successful indices of the same parity therefore have congruent squares of their coordinates modulo $\ell^{2h}$. Factoring the difference of squares gives $X_n\equiv X_m$ or $X_n\equiv-X_m$ modulo $\ell^h$. This argument also works when both factors are divisible by $\ell$. [Pell identity](HosoyaEvenDiagonalSeparation.lean) · [Square-root congruence](HosoyaLocalSquareRoots.lean)

Within either coordinate class, the value and coordinate agree. Their determinant at a gap $j$ is $-22(-1)^nF_j$. At most one power of $\ell$ is lost on removing 22. Along the fixed step $d$, there is an offset $a$ such that $\ell^{a+b}\mid F_{dt}$ forces $\ell^b\mid t$, for every $b,t$. For example, one can take the $\ell$-adic valuation of $F_{de}$ where $e$ is the first positive return with $\ell^2\mid F_{de}$. The proof uses the exact growth of the return rank on a step of known valuation. The same constant works for every $r$ and $y$. [Determinant and index recovery](HosoyaPrimePowerCollisions.lean) · [Rank growth](LucasFibonacciPrimePowerLifts.lean)

Prime parameters above $\max(2,\ell)$ have the same parity and belong to reduced classes modulo $\ell^b$. The normalized prime mass of each reduced class tends to $1/\varphi(\ell^b)$ by Dirichlet’s theorem. There are only finitely many classes at each level, so the neighborhood of 1 can be chosen before specifying $r$ or $y$. The finitely many excluded prime parameters contribute zero limiting mass. [Mass argument](HosoyaPrimePowerUniformMass.lean)

## The exponent at 13 is sharp

On the **original sequence at prime indices** ($r=0,d=1$), for every $b\ge0$ there is a residue $y_b$ modulo $13^{2b+4}$ whose accepted prime parameters contain one entire reduced class modulo $364\cdot13^b$. Its normalized mass is eventually at least $1/(728\cdot13^b)$. Since the square root of the testing modulus is $13^{b+2}$, no uniform upper rate $o(M^{-1/2})$ is possible at 13. The target residue is allowed to vary with $b$. [Reduced-class construction](HosoyaThirteenCriticalClass.lean) · [Matching mass bound](HosoyaCriticalPrimeMass.lean)

The coordinate sequence starts $7,6,13,19,\ldots$. Its term at index 23 is divisible by $13^2$, and $F_{364}$ is divisible by $13^2$ exactly. For each $b$, a lifting argument produces a reduced class modulo $364\cdot13^b$ inside $q\equiv23\pmod{364}$ with $13^{b+2}\mid X_q$. On that class $U(q)\equiv12\pmod{13}$. The Pell identity squares the coordinate divisibility and the sum of any two upper values in the class is a unit at 13. This makes the upper value constant modulo $13^{2b+4}$. At $b=0$ one obtains the class $23\bmod364$ and the residue $18095\bmod28561$. [Arithmetic certificate](HosoyaThirteenCriticalClass.lean)

## Scope and checks

The pinned declaration asks whether infinitely many distinct prime numbers occur as actual $U(n)$ at unrestricted nonnegative indices. These local frequency bounds concern the primality of the **parameter** $q$ and leave that infinitude open. Carlip and Somer studied residue frequencies of second-order recurrences modulo prime powers. Bragman and Rowland studied the proportion of attained residues for Fibonacci numbers. The quantities here are the concentration of the upper Hosoya values at prime parameters and the explicit lower bound for their mass at 13. [Pinned question](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Ching et al.](https://arxiv.org/abs/2211.10788) · [Carlip and Somer](https://dml.cz/dmlcz/134189) · [Limiting density of Fibonacci residues](https://doi.org/10.1007/s40993-025-00667-1)

An independent modular calculation tested 950,400 indices over eleven primes, six steps, four offsets and three precision levels. Each fixed-parity fiber occupied at most two predicted index classes. At 13, seven successive levels were lifted independently, and all 64 tested translates of each class gave the same upper residue.

Lean 4.33.1 rebuilt all 26 notebook modules from clean output and replayed each with the kernel checker. All 85 named axiom reports use only `propext`, `Classical.choice` and `Quot.sound`. The notebook index check and all five repository tests passed. The pinned upstream statement matches the live source blob. Searches of DeepMind and Open Math Agents issues and pull requests and 11,219 Left to Solve records found the prime-values question and its statement PR. No matching formalization of the concentration and sharpness results appeared. Codex assisted with the proof. [Notebook replay](../../README.md#replay) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/8156) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents) · [Left to Solve](https://lefttosolve.com/api/solved)
