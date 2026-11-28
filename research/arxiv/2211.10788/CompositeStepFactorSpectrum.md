# Factor degrees at arbitrary Hosoya index steps

For the upper Hosoya diagonal write $U(r)=2F_r+F_{r+2}$. At offset $r$ and positive step $d$, its homogeneous index form satisfies $H(F_n,F_{n+1})=U(r+d(n+1))$. Put $P(X)=H(X,1)$. For every prime $p$ other than 5 and 11, the following bounded test gives exactly the degrees of the irreducible factors of $P$ over $\mathbf F_p$. The step may be composite or divisible by $p$, and the leading coefficient $U(r)$ may vanish modulo $p$. [Index forms](IndexForms.md) · [Lean theorem](HosoyaCompositeFactorSpectrum.lean) · [Pinned upper diagonal](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean)

In the quadratic algebra $\mathbf F_p[\omega]/(\omega^2-\omega-1)$, set $S=U(r+1)-U(r)+U(r)\omega$. Let $m$ be the least positive exponent for which the coefficient of $\omega$ in $S^m$ vanishes. This exponent exists and is at most $p+1$. Set $s=-p$ if $p\equiv 2,3\pmod 5$ and $s=p$ otherwise. The degree set consists of
\[
  \operatorname{ord}_t(s)\qquad
  \left(2\le t\le d(p+1),\quad p\nmid t,\quad \frac{t}{\gcd(t,d)}=m\right).
\]
Here $\operatorname{ord}_t$ denotes multiplicative order modulo $t$. For example, $(p,r,d)=(7,0,9)$ gives $m=2$. The admissible orders are 2, 6 and 18, and the corresponding degrees are 1, 2 and 6. The theorem gives the set of degrees. It leaves multiplicities and the number of factors of each degree unspecified. [Bounded criterion](HosoyaCompositeFactorSpectrum.lean)

## Why every listed degree occurs

Take the two roots $a,b$ of $X^2-X-1$ in an algebraic closure and put $A=(3+a)a^r$, $B=(3+b)b^r$. They are nonzero in the stated characteristics. The affine root equation in the coordinate $w=(x+a)/(x+b)$ is $w^d=B/A$. The omitted value $w=1$ is the point at infinity, even when the leading coefficient vanishes. The two evaluations of $S$ are $A,B$, hence $m$ is the multiplicative order of $B/A$. Frobenius fixes or interchanges $a,b$ according to $p\bmod 5$, so the orbit through a coordinate of order $t$ has length $\operatorname{ord}_t(s)$. [Affine fiber and base-field coefficient test](HosoyaCompositeFactorSpectrum.lean) · [Frobenius action](HosoyaFactorDegrees.lean)

Conversely, let $t$ satisfy the test and take a primitive $t$th root of unity $z$. Then $z^d$ and $B/A$ have order $m$. They differ by raising to an exponent coprime to $m$. The reduction map from units modulo $t$ onto units modulo $m$ lifts that exponent to one coprime to $t$. Raising $z$ to the lifted exponent gives a solution $w$ of exact order $t$. Since $t>1$, the inverse transformation gives an affine root, whose minimal polynomial realizes the predicted degree. The previous prime-step factor formula used a marked rational projective zero. [Realization proof](HosoyaCompositeFactorSpectrum.lean) · [Prime-step theorem](PrimeStepFactorDegrees.md)

## Scope and verification

The main declaration is `Arxiv.«2211.10788».upperIndexPolynomial_factor_degree_spectrum`. Its hypotheses are primality of $p$, $p\ne5,11$ and $d>0$. The notebook classifies local factors of the polynomials representing subsequences. Infinitude of prime values of $U$ remains open. The finite-field method has antecedents in the study of composed polynomials. [Ching et al.](https://arxiv.org/abs/2211.10788) · [Brochero Martínez, Reis and Silva](https://arxiv.org/abs/1901.02951) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/8156)

Lean 4.33.1 rebuilt all 12 notebook modules from fresh output, and each passed an independent kernel replay. The 51 named axiom reports used only `propext`, `Classical.choice` and `Quot.sound`. An independent calculation compared the predicted degrees against the degrees of $\gcd(P,X^{p^e}-X)$ for $1\le e\le d$ in 378 composite-step examples, including cases with $p\mid d$. Searches of open and closed DeepMind and Open Math Agents issues and PRs and 6,290 Left to Solve records found no matching formalization. Codex assisted with the formalization. [OMA search](https://github.com/lefttosolve2/open-math-agents/issues?q=Hosoya) · [LTS records](https://lefttosolve.com/api/solved) · [Kernel replay](../../README.md#replay)
