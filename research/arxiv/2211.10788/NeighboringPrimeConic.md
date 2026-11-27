# Neighboring prime pairs on a conic

For ordered primes `p < q`, the lower and upper Lucas–Fibonacci neighbors equal `p` and `q` at a common index `n ≥ 2` if and only if

```text
11(p + q)² = 49(pq + 1).
```

Thus a third prime pair in the question of Ching, Flórez, Luca, Mukherjee and Saunders exists exactly when this conic has a positive ordered prime point other than `(2,5)` and `(19,37)`. Existence of a third point remains open. The paper reports a search through index 80,000. DeepMind’s pinned conjecture concerns prime values on the upper diagonal alone. [Paper, p. 3](https://arxiv.org/pdf/2211.10788#page=3) · [upstream declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Lean proof](NeighboringPrimeConic.lean)

**All integer points.** For `0 < p < q`, the same equation characterizes the neighboring pairs at **positive even** indices, with no primality hypothesis. Write `Vₙ = Fₙ + Lₙ₋₁` and `Uₙ = Fₙ + Lₙ₊₁`. The recurrence gives `Vₙ + Uₙ = 7Fₙ`, while Cassini’s identity gives `Vₙ Uₙ = 11Fₙ² − 1` at even indices. Eliminating `Fₙ` gives the conic. The previous neighboring-prime criterion shows that every simultaneous prime pair has even index. [Product identity and parity restriction](NeighboringPrimePairs.md)

**Recovering the index.** The equation forces `7 ∣ p+q`. Set `f = (p+q)/7` and `b = q−3f`. Then `p+b = 4f` and `q = 3f+b`. Substitution gives `b² − fb − f² = 1`. Every nonnegative solution of this norm equation is a consecutive Fibonacci pair `(F₂ₖ,F₂ₖ₊₁)`. Indeed, when `f > 0`, the norm forces `f < b ≤ 2f`. The inverse step `(f,b) ↦ (2f−b,b−f)` preserves the norm and decreases the first coordinate. The only solution with first coordinate zero is `(0,1)`. Reversing the steps recovers the even index and both original neighbors.

The declarations `Arxiv.«2211.10788».even_neighbors_iff_conic` and `Arxiv.«2211.10788».neighboring_prime_pair_iff_conic` use the pinned upper diagonal and the [lower-neighbor definition](NeighboringLucasFibonacciPrimes.lean). The [notebook replay](../../README.md#replay) builds their dependency. Both declarations print only `propext`, `Classical.choice` and `Quot.sound` under Lean 4.33.1.

Open and closed DeepMind and OMA searches covered the paper, the sequence and the quadratic-form and neighboring-pair formulations. The DeepMind matches specify the upper diagonal. No matching conic formalization surfaced in those results or in the LTS solved records. Codex assisted with the formalization. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [statement PR](https://github.com/google-deepmind/formal-conjectures/pull/8156) · [OMA search](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%222211.10788%22) · [LTS records](https://lefttosolve.com/api/solved)
