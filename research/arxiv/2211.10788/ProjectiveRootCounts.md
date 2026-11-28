# Local root counts for the upper Hosoya index forms

For every prime `p`, offset `r ≥ 0`, and step `d ≥ 1`, the following formulas count **all distinct projective roots** of the upper index form `H(r,d;x,y)` modulo `p`. Here `U(r) = 2Fᵣ+Fᵣ₊₂` is the pinned upper Lucas–Fibonacci term. The form represents `U(r+d(n+1))` at the Fibonacci pair `(Fₙ,Fₙ₊₁)`. The points being counted are the `p` affine points `(x,1)` and the point at infinity `(1,0)`. [Main declarations](HosoyaLocalRootCounts.lean) · [Index forms and specialization](IndexForms.md) · [Ching et al., introduction](https://arxiv.org/pdf/2211.10788#page=3)

Work in the algebra over the field of `p` elements with `ω² = 1+ω`. Set `T = U(r+1)−U(r)+U(r)ω`. For `p ≠ 5,11`, take `N = p+1` if `p ≡ 2,3 (mod 5)` and `N = p−1` otherwise. Put `g = gcd(d,N)` and `e = N/g`.

| Prime and degree | Number of projective roots |
| --- | --- |
| `p ≠ 5,11` | `g` if the coefficient of `ω` in `Tᵉ` vanishes, otherwise 0 |
| `p = 11` | 1 |
| `p = 5, d = 1` | 1 |
| `p = 5, d ≥ 2, 5 ∤ d` | 2 |
| `p = 5, 5 ∣ d` | 6 if `5 ∣ U(r)`, otherwise 1 |

For the affine polynomial `P(X) = H(r,d;X,1)`, subtract one from the table exactly when `p ∣ U(r)`. For example, at `p = 7, d = 4`, offsets 0 and 4 both have four projective roots. Offset 0 has four affine roots and offset 4 has three, since `U(4) = 14`. Offset 1 has no roots. The earlier fixed-divisor test characterized when every pair is a root. This count also distinguishes all the intermediate cases. [Affine root theorem](HosoyaLocalRootCounts.lean) · [Fixed divisors](FixedDivisors.md)

## Why the count is a gcd

When the Fibonacci quadratic splits, its two roots `a,b` give two linear forms `x+ay` and `x+by`. Their ratio identifies the projective points away from the two zero lines with the multiplicative group of order `p−1`. At an ordinary prime both conjugates of `T` are units. The form vanishes exactly when the ratio raised to `d` equals the ratio of those conjugates. In a cyclic group of order `N`, a target has `gcd(d,N)` roots if its `N/gcd(d,N)` power equals one, and zero roots otherwise. [Split-prime proof](HosoyaSplitProjectiveRoots.lean) · [Cyclic power map](HosoyaProjectivePowerFibers.lean)

When the quadratic is irreducible, the algebra is the field of `p²` elements. Each projective point has `p−1` nonzero representatives. The condition on a representative `z` is that `Tzᵈ` belong to the nonzero scalars, equivalently `(Tzᵈ)^(p−1) = 1`. Counting this power-map fiber and dividing by `p−1` gives the same test with `N = p+1`, including `p = 2`. At 11 the form is `4ʳ(x+4y)ᵈ`. At 5 it is `(x+3y)^(d−1) [U(r)(x+3y)+d·3ʳy]`. These identities give the two exceptional counts directly. [Inert-prime proof](HosoyaInertProjectiveRoots.lean) · [Reductions at 5 and 11](HosoyaProjectiveRoots.lean)

A zero count excludes divisibility on every Fibonacci input pair, since consecutive Fibonacci numbers are coprime. A positive count leaves a further question about which points the Fibonacci pairs visit. For instance, a degree-one form has a projective root modulo 47, while 47 divides no upper term. The pinned question of infinitely many primes equal to whole upper values remains open. [Progression divisor criterion and the example at 47](ProgressionDivisors.md) · [Pinned DeepMind declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean)

The main results in `Arxiv.«2211.10788»` are `upperProjectiveRootCount_ordinary`, `upperProjectiveRootCount_five`, `upperProjectiveRootCount_eleven`, and `upperProjectiveRootCount_affine`. Independent replay on Lean 4.33.1 checked nine notebook modules and 25 named axiom reports. Only `propext`, `Classical.choice`, and `Quot.sound` occurred. Direct enumeration also checked 8,008 prime, offset and degree triples. Searches of DeepMind and Open Math Agents issues and PRs and Left to Solve’s solved records found the upper prime-values question and no matching root-count formalization. Codex assisted with the formalization. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents) · [Left to Solve](https://lefttosolve.com/api/solved) · [Notebook replay](../../README.md#replay)
