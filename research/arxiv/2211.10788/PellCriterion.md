# A Pell criterion for the upper Lucas–Fibonacci diagonal

Write `Sₙ = 2Fₙ + Fₙ₊₂ = Fₙ + Lₙ₊₁`. A natural number `y` occurs among the `Sₙ` **if and only if** there is a natural number `x` such that

```text
x ≡ 7y (mod 22)    and    x² − 5y² ∈ {44, −44}.
```

Consequently the pinned conjecture is equivalent, without hypotheses, to infinitude of primes `p` satisfying this test with `y = p`. The proof uses the type of the upstream declaration and leaves the infinitude question open. [Lean declarations](LucasFibonacciPellCriterion.lean) · [pinned upstream statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Ching et al., p. 3](https://arxiv.org/pdf/2211.10788#page=3)

For consecutive terms `(a,b)`, the recurrence takes `(a,b)` to `(b,a+b)`. This move changes the sign of `b² − ab − a²` and preserves `b ≡ 4a (mod 11)`. The initial pair `(1,4)` has norm 11. Putting `x = 2b − a` gives the square equation and the congruence modulo 22.

For the converse, set `a = y` and `b = (x+y)/2`. The congruence gives an integral pair satisfying the norm and residue conditions, and it also forces `x > y`, hence `b > a`. Indeed, `x ≤ y` would force `4y² ≤ 44`, and checking `0 ≤ x ≤ y ≤ 3` leaves no solution satisfying the congruence. While `b < 2a`, the inverse move `(a,b) ↦ (b−a,a)` decreases the first coordinate. At the first pair with `b = 2a+e`, the norm gives `a² + 3ae + e² = 11`. Thus `a,e ≤ 3`. The possible pairs `(a,b)` are `(1,4)` and `(2,5)`, and only the first satisfies the residue condition. Reversing the descent recovers the index. The prime `y = 2` has the square witness `x = 8` on the other orbit. This example shows why the square equation alone admits extra primes.

The upper diagonal begins `1,4,5,9,…`, the tail of the Lagarias sequence `3,1,4,5,…`. Moree and Stevenhagen study primes dividing terms of that sequence. The criterion here concerns primes equal to terms. [Moree and Stevenhagen](https://arxiv.org/abs/math/9912253)

The two exported declarations are `Arxiv.«2211.10788».exists_lucasFibonacciSum_iff_pell` and `Arxiv.«2211.10788».lucasFibonacci_prime_values_iff_pell`. Both print only `propext`, `Classical.choice` and `Quot.sound` in Lean 4.33.1. The [notebook replay](../../README.md#replay) includes this file.

Open and closed DeepMind and OMA issue and PR searches covered the paper identifier, the upstream sequence and the Lagarias and OEIS names. The DeepMind matches were the statement issue and its merged PR. No matching formalization appeared there, in OMA or in the LTS solved records searched. Codex assisted with the formalization. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [statement PR](https://github.com/google-deepmind/formal-conjectures/pull/8156) · [OMA search](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%222211.10788%22) · [LTS solved records](https://lefttosolve.com/api/solved)
