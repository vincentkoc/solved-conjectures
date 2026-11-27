# Prime divisors of Lucas–Fibonacci sums

**Partial upstream coverage.** Write `S(n) = 2 * Nat.fib n + Nat.fib (n + 2)`. The checked theorem `Arxiv.«2211.10788».infinite_prime_divisors_of_composite_lucasFibonacciSum` proves that for every natural offset `r` and positive step `d`, infinitely many distinct primes divide a composite `S(r + d*k)` for some natural `k`.

At `f606af160664c5a10952e9a957b100a1cd45bbeb`, `Arxiv.«2211.10788».infinitely_many_lucas_fibonacci_sum_primes` asks for infinitely many primes **equal** to some `S(n)`. That question remains open. The proof imports the sequence definition directly from the pinned upstream module. [Upstream file](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Ching et al., introduction](https://arxiv.org/pdf/2211.10788#page=3)

**Method.** Fix a bound `B` and take `a = S(r+d) > 1`. The Fibonacci step `(x,y) ↦ (y,x+y)` permutes the pairs modulo `a * B!`. A positive multiple of its return time stays in the index progression. Strict growth makes the later term `a * (1 + j * B!)` with `j > 0`. Every prime divisor of the cofactor exceeds `B`. This specializes the modular argument for prime divisors of recurrences to composite terms on this diagonal. [Lin, Theorems 2.1–2.2](https://arxiv.org/pdf/1706.09102#page=2)

**Duplicate check, 2026-11-28.** Open and closed DeepMind and OMA searches by declaration, title, path, arXiv ID and OEIS A091157 found the DeepMind statement issue and merged statement PR. OMA returned no matching PR or issue. The LTS solved API had no matching record among 3,143 entries. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [DeepMind PR](https://github.com/google-deepmind/formal-conjectures/pull/8156) · [OMA search](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%222211.10788%22) · [LTS solved list](https://lefttosolve.com/api/solved)

Replay from the research worktree root. The axiom report contains only `propext`, `Classical.choice` and `Quot.sound`.

```sh
proof="$PWD/research/arxiv/2211.10788/LucasFibonacciPrimeDivisors.lean"
source ~/formal-math/env.sh && cd ~/formal-math/fc && lake build 'FormalConjectures.Arxiv.«2211.10788».LucasFibonacciSumPrimes' && lake env lean "$proof"
```
