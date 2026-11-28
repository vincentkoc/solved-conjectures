# Finite prime covers on the upper Hosoya diagonal

Write `U(n) = 2Fₙ + Fₙ₊₂`. A finite set of primes covers the index progression `r + dt` when at least one prime in the set divides each term. For every offset `r` and budget `k`, there is a finite list of candidate primes and a positive period `T`, both independent of the step. For **every** `d ≥ 0`, a cover with at most `k` primes exists exactly when some set of at most `k` candidates divides all the terms at parameters `0 ≤ t < T` for step `d mod T`. Thus the answer as a function of the step is periodic from zero. [Lean proof](LucasFibonacciPrimeCovers.lean)

## One or two primes

The two smallest budgets have short exact tests.

| Budget | Condition for a cover of the whole progression |
| --- | --- |
| One prime | `gcd(U(r), F_d) > 1` |
| Two primes | Both `gcd(U(r), F_(2d)) > 1` and `gcd(U(r+d), F_(2d)) > 1` |

A progression can consist entirely of composites even when its terms have gcd 1. At `r = 7, d = 34`, the prime 3 divides every term with even parameter, and 67 divides every term with odd parameter. Indeed 3 divides `U(7) = 60`, 67 divides `U(41)`, and both divide `F₆₈`. On the other hand `gcd(60, F₃₄) = 1`. The formal example also rules out equality to either covering prime at every index.

## Why the candidate list is finite

If at most `k` primes cover the progression, some prime dividing its first term divides another term at a positive parameter at most `k!`. To see this, two of the first `k+1` parameters share a covering prime `q`. Their gap `g` satisfies `1 ≤ g ≤ k`, and `q` divides `F_(dg)`. Consequently a shift of `dg` preserves divisibility by `q` at every index. If `q` divides the first term, the shift gives the second hit immediately. Otherwise the entire subprogression of step `dg` through that first term avoids `q`. Induction with the remaining primes gives a return within `g(k−1)!` original steps. The same argument applies starting at every term.

Let `ω² = ω+1`, and let `B(r,e)` be the coefficient of `ω` in `((3+ω)ωʳ)ᵉ`. Take 5 together with the prime divisors of all `B(r,e)` for `1 ≤ e ≤ k!`. These coefficients are positive. At every term of a covered progression the preceding argument finds a prime with Fibonacci return rank at most `k!`. The notebook’s divisor criterion puts that prime in the candidate list. Intersecting the original cover with the list therefore still covers the progression. [Progression divisor criterion](ProgressionDivisors.md)

Let `M` be the product of the candidates, and take `T` to be the first positive Fibonacci index with `M ∣ F_T`. Shifting an index by any multiple of `T` preserves divisibility by each candidate. Both the step and the parameter can therefore be reduced modulo `T`. The bound is finite and can grow quickly. For budget two, every gap of size one or two divides two, so each parity class has its own fixed prime. This yields the two-gcd test above.

## Scope and sources

Ching, Flórez, Luca, Mukherjee and Saunders ask whether infinitely many primes equal a term of the upper diagonal. A cover confines all prime values on its progression to the covering set. The finite decision above concerns the existence of a cover for a given budget. Prime-value infinitude for the whole upper diagonal remains open. [Paper, introduction and §5](https://arxiv.org/abs/2211.10788) · [Pinned DeepMind declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean)

Classical covering-system theory gives the sharper bound `2^(k−1)` for every modulus in a minimal cover by `k` residue classes. Balister, Bollobás, Morris, Sahasrabudhe and Tiba derive it from the interval-cover theorem of Crittenden and Vanden Eynden. An existing Lean formalization covers that interval theorem. The direct factorial argument here supplies the finite candidate primes for the fixed Hosoya offset and the common period across all steps. Dubickas, Novikas and Šiurys study composite binary recurrences constructed by choosing the initial pair. Here the sequence is fixed. [Balister et al.](https://doi.org/10.1007/s10474-019-00980-z) · [Formalization of Erdős 275](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos275.lean) · [Dubickas, Novikas and Šiurys](https://web.vu.lt/mif/j.siurys/files/2013/10/sdarticle.pdf)

Lean 4.33.1 compiled the pinned upstream file and three notebook modules in fresh output. Separate `leanchecker` calls replayed all three. The five new declarations and eight dependency reports use only `propext`, `Classical.choice` and `Quot.sound`. [Notebook replay](../../README.md#replay)
