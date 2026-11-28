# Which primes divide a Lucas–Fibonacci index progression?

Fix nonnegative integers `r,d` and write `U(n) = 2Fₙ + Fₙ₊₂`. For every prime `p`, the following test decides whether **some `U(r+dt)` is divisible by `p`**. The case `d=0` includes a single fixed term. DeepMind’s open conjecture asks whether infinitely many primes equal a term. A positive divisor test alone leaves that equality undecided. [Pinned definition and conjecture](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Ching et al., introduction](https://arxiv.org/pdf/2211.10788#page=3)

| Prime | Test |
| --- | --- |
| `5` | A term is divisible exactly when `5 ∤ d` or `r ≡ 2 (mod 5)`. |
| `11` | No term is divisible. |
| Every other prime | Let `e` be the least positive `t` such that `p ∣ F_{dt}`. Expand `((3+w)wʳ)ᵉ = A + B w` using `w²=w+1`. A term is divisible exactly when `p ∣ B`. |

The return rank `e` depends only on the prime and the step. It exists because the Fibonacci pair step permutes residue pairs. The coefficients of the power may be reduced modulo `p` throughout. For the full sequence and `p=47`, Lean checks `e=16` and `B ≡ 8 (mod 47)`. Hence 47 divides no term, although its residue 3 modulo 44 passes the earlier five-class exclusion. [Lean proof](LucasFibonacciProgressionDivisors.lean) · [Earlier exclusion](ExcludedPrimeDivisors.md)

For the ordinary primes, let `a,b` be the two roots of `X²−X−1` in an algebraic closure of the residue field. Their difference is nonzero when `p ≠ 5`, and `(3+a)(3+b)=11` handles the other exceptional prime. Two evaluations of a quadratic expression agree exactly when its coefficient of `w` vanishes. The coefficient of `w` in `(3+w)wⁿ` equals `U(n)`, and in `wⁿ` equals `Fₙ`. Thus the progression advances by the field element `(a/b)ᵈ`, whose multiplicative order is `e`. A hit exists exactly when the ratio of the initial evaluations is an `e`th root of unity. This gives the coefficient test in the table. Moree and Stevenhagen use the underlying root-quotient criterion for the Lagarias sequence starting with `3,1`. The upper diagonal here is its tail starting with `1,4`. [Moree and Stevenhagen, §1](https://www.numdam.org/item/JTNB_2001__13_1_241_0/)

The second theorem locates repeated occurrences for **any positive modulus `m`**. If `m ∣ U(s)`, then `m ∣ U(s+dt)` exactly when the Fibonacci return rank for `m,d` divides `t`. The two coefficients of `(3+w)wˢ` are coprime, so after a hit divisibility reduces to `m ∣ F_{dt}`. The Fibonacci gcd identity identifies those steps as precisely the multiples of the first positive return.

The exported theorems in `Arxiv.«2211.10788»` are `prime_dvd_lucasFibonacciSum_on_progression_iff` and `lucasFibonacciSum_dvd_after_hit_iff`. Both use the canonical `lucasFibonacciSum` and report only `propext`, `Classical.choice` and `Quot.sound`. Live searches of DeepMind and OMA issues and PRs and the LTS solved records returned no matching formalization. Codex assisted with the proof. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [DeepMind statement PR](https://github.com/google-deepmind/formal-conjectures/pull/8156) · [LTS solved records](https://lefttosolve.com/api/solved) · [Notebook replay](../../README.md#replay)
