# Large prime factors of Lucas–Fibonacci values on progressions

Let `Uₙ = Fₙ + Lₙ₊₁ = 2Fₙ + Fₙ₊₂`, the sequence called `lucasFibonacciSum` in the pinned DeepMind file. Fix `r ≥ 0` and `d ≥ 1`. For every real sequence `e(n) → 0`, the proportion of `t < N` for which **all** prime factors of `Uₙ` are at most `e(n) n log n`, with `n = r + dt`, tends to zero. For example, a density-one set of terms has a prime factor exceeding `n √(log n)`. The threshold can oscillate. The upstream question asks whether infinitely many entire terms are prime and remains open. [Lean proof](LucasFibonacciLargeFactors.lean) · [Pinned DeepMind definition and prime-values question](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Ching et al.](https://arxiv.org/abs/2211.10788)

The proof gives a finite estimate. For a finite subset `T ⊆ [a, a+L)`, put `u(t) = U(r+dt)`. Then

```text
∏_{t∈T} u(t) divides lcm_{t∈T} u(t) · (∏_{j=1}^L F_{dj})².
```

For each prime dividing the product, choose an index where its valuation is maximal. Its power at any other index divides the Fibonacci number at the difference of the two sequence indices. A given gap occurs at most once to the left and once to the right of the chosen index, which accounts for the square. If every prime factor of every selected term belongs to a finite set `P`, growth estimates for the Fibonacci numbers and the lcm give

```text
d a |T| ≤ 2(r + d(a+L) + 3) |P| + 4dL².
```

Partitioning the first `N` indices into intervals yields a density statement for arbitrary prime sets. Whenever `|P_N|/N → 0`, the proportion of `t < N` with every prime factor of `U(r+dt)` in `P_N` tends to zero. Chebyshev’s bound for prime counting gives the displayed greatest-prime-factor threshold. [Source for the shared-divisor identity](LucasFibonacciProgressionDivisors.lean) · [Earlier dyadic-block estimate](SmoothBlocks.md)

The greatest-prime-factor threshold specializes Stewart’s 1982 Theorem 3 on binary recurrences. His later Theorem 2 gives a stronger almost-all estimate. The Lean proof derives the bounds directly for this sequence. [Stewart, 1982, Theorem 3](https://uwaterloo.ca/pure-mathematics/sites/default/files/uploads/documents/10.1515_crll.1982.333.12.pdf) · [Stewart, later Theorem 2](https://uwaterloo.ca/pure-mathematics/sites/default/files/uploads/documents/onprimef.pdf#page=3)

The five declarations in `Arxiv.«2211.10788»` are `lucasFibonacciSum_prod_dvd_lcm_mul_fib`, `lucasFibonacciSum_smooth_interval_bound`, `sparse_prime_support_density_zero`, `sub_n_log_n_smooth_density_zero`, and `progression_sub_n_log_n_smooth_density_zero`. Each uses only `propext`, `Classical.choice`, and `Quot.sound`. Searches of DeepMind and Open Math Agents issues and pull requests and the Left to Solve solved records returned no matching formalization. Codex assisted with the proof. [DeepMind tracking issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [Left to Solve](https://lefttosolve.com/api/solved) · [Notebook replay](../../README.md#replay)
