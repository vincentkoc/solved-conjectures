# Which values belong to either Lucas–Fibonacci diagonal?

Let `Uₙ = Fₙ + Lₙ₊₁` for `n ≥ 0` and `Vₙ = Fₙ + Lₙ₋₁` for `n ≥ 1`. For a natural number `y`, a **witness** is a natural number `x` satisfying `x² − 5y² = 44` or `x² − 5y² = −44`.

| Values of `y` | Exact test |
| --- | --- |
| Either diagonal | A witness exists. |
| Upper diagonal | A witness satisfies `x ≡ 7y (mod 22)`. |
| Lower diagonal | A witness satisfies `x ≡ −7y (mod 22)`. |
| Both diagonals, allowing different indices | `y = 5`. |

At `y = 5`, the upper witness is 13 and the lower witness is 9. The lower value at index one is 3, with witness 1. Thus a test that required `x > y` would miss this endpoint. The upper criterion was proved in the [previous notebook result](PellCriterion.md). The [new Lean proof](LucasFibonacciDiagonalUnion.lean) establishes the other three rows.

Ching et al. ask about primes of the two forms and separately about two prime neighbors at the same index. DeepMind’s `infinitely_many_lucas_fibonacci_sum_primes` asks about the upper diagonal. The set of primes passing the bare square test is infinite exactly when the pinned upper assertion holds **or** the lower diagonal has infinitely many prime values. These infinitude questions remain open. [Source, p. 3](https://arxiv.org/pdf/2211.10788#page=3) · [pinned upper declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [same-index prime-pair criterion](NeighboringPrimeConic.md)

**Recovering the two sequences.** For a witness, parity gives an integer `b = (x+y)/2`. The pair `(y,b)` has `b² − yb − y² = ±11`. When `y ≥ 4`, one has `y < b < 2y`, and the inverse Fibonacci step `(y,b) ↦ (b−y,y)` preserves the absolute norm and decreases the first coordinate. For `y ≤ 3`, the norm and `y ≤ 2b` leave exactly the pairs `(1,4)`, `(2,5)`, and `(3,2)`. The first starts the upper sequence. The last two are consecutive states on the lower sequence. For the latter, each successor satisfies `b ≡ −3y (mod 11)`, which gives the negative residue for `x`. The two possible residue tests cannot hold for the same witness: they would force both `x` and `y` to be divisible by 11, contrary to the norm 44.

**Ruling out other overlaps.** The gap identities are `Vₙ₊₂ − Uₙ = Fₙ₊₁` for `n ≥ 0` and `Uₙ − Vₙ₊₁ = 2Fₙ₋₂` for `n ≥ 2`. For `n ≥ 3` the upper value lies strictly between two consecutive values of the increasing lower tail. At the small indices, `U₂ = V₃ = 5` is the only common value.

The exported declarations are `either_diagonal_iff_pell`, `lower_diagonal_iff_pell`, `both_diagonals_iff_five` and `pooled_prime_values_iff` in namespace `Arxiv.«2211.10788»`. The [notebook replay](../../README.md#replay) compiles the lower-neighbor dependency and audits their axioms.

Open and closed DeepMind and OMA searches covered the paper identifier, OEIS A091157 and A153892, and the intersection and Pell formulations. The DeepMind matches concerned the upper statement. No matching formalization of the pooled or lower criterion appeared there or in the LTS solved records searched. Codex assisted with the formalization. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [statement PR](https://github.com/google-deepmind/formal-conjectures/pull/8156) · [OMA search](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%222211.10788%22) · [LTS records](https://lefttosolve.com/api/solved)
