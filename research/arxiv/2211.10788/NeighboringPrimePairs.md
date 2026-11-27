# A semiprime criterion for neighboring Lucas–Fibonacci primes

Ching, Flórez, Luca, Mukherjee and Saunders ask whether any index beyond their two examples gives primes on both neighboring diagonals. Put `Uₙ = Fₙ + Lₙ₊₁` and `Vₙ = Fₙ + Lₙ₋₁`. Their examples have indices 2 and 6 and unordered pairs {2, 5} and {19, 37}. The pinned DeepMind declaration asks for infinitely many prime values of `Uₙ` alone. [Paper, introduction](https://arxiv.org/pdf/2211.10788#page=3) · [upstream declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean)

For every `n ≥ 2`, **both neighbors are prime** if and only if either `n = 2`, or both of the following hold.

- The residue of `n` modulo 24 is 0, 6 or 18.
- The integer `11Fₙ² − 1` has exactly two prime factors counted with multiplicity.

Thus another pair exists precisely if the semiprime condition holds at some `n > 6` in those three classes. The existence of such an index remains open. [Lean proof](NeighboringLucasFibonacciPrimes.lean)

**Factorization.** The upper neighbor is the original `lucasFibonacciSum n`. For `n = m + 2`, the lower neighbor is `2Fₙ + Fₘ` because `Lₘ₊₁ = Fₘ + Fₘ₊₂`. Cassini's identity gives `Uₙ Vₙ = 11Fₙ² − (−1)ⁿ`. On even indices this is `11Fₙ² − 1`. Both factors exceed one, so their product is semiprime exactly when they are both prime.

**Residue test.** The Fibonacci recurrence modulo 42 returns to its initial state after 48 steps. Lean checks the two initial congruences, propagates them to every index by induction, and checks the 48 residues. Exactly the three classes above have `gcd(Uₙ Vₙ, 42) = 1`. For `n ≥ 8`, both neighbors exceed 42, so prime neighbors must pass this test. Direct checks cover indices 2 through 7. At the two smaller nonnegative indices the upstream upper neighbor is 1 or 4.

The three declarations in `Arxiv.«2211.10788»` are `lucasFibonacciSum_mul_lowerNeighbor`, `neighboring_product_coprime_42_iff` and `neighboring_primes_iff_semiprime`. The last uses Mathlib's `Nat.IsAlmostPrime 2`. Replaying the file with Lean 4.33.1 prints all three axiom reports. Use the [notebook environment](../../README.md#replay) and run `lake env lean "$notebook/arxiv/2211.10788/NeighboringLucasFibonacciPrimes.lean"`.

Open and closed DeepMind and OMA searches covered the paper, the upstream declaration, the neighboring-pair terminology and both OEIS identifiers. The searches found the upper-neighbor issue and merged PR. No matching Lean reduction appeared there or among the LTS solved records. Codex assisted with this formalization. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [statement PR](https://github.com/google-deepmind/formal-conjectures/pull/8156) · [OMA search](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%222211.10788%22) · [LTS solved records](https://lefttosolve.com/api/solved)
