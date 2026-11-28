# Every square on the Lucas–Fibonacci diagonals

The upper diagonal `Uₙ = Fₙ + Lₙ₊₁` takes square values at exactly three indices. The lower diagonal `Vₙ = Fₙ + Lₙ₋₁`, defined for `n ≥ 1`, has one square. These are the square cases of the two families in Ching et al. The classification follows Cohn's 1968 solution of two quartic Diophantine equations. The Lean proof establishes the classification directly from the recurrences. [Lean proof](LucasFibonacciSquareValues.lean) · [Ching et al., p. 3](https://arxiv.org/pdf/2211.10788#page=3) · [Cohn, pp. 238–241](https://msp.org/pjm/1968/26-2/pjm-v26-n2-p03-p.pdf)

| Diagonal | Index | Square |
| --- | --- | --- |
| Upper | 0 | 1 |
| Upper | 1 | 4 |
| Upper | 3 | 9 |
| Lower | 9 | 81 |

In particular, the only prime powers of even positive exponent in the upper sequence are 4 and 9. The upstream declaration asks whether the set of **prime values** of `Uₙ` is infinite. That question and the classification of odd-exponent prime powers remain open here. [Pinned definition and question](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Earlier local prime-power divisibility criterion](PrimePowerLifts.md)

## Excluding a second square

Let `s` satisfy the Fibonacci recurrence, and put `T₀ = 3`, `Tᵣ₊₁ = Tᵣ² − 2`. Two applications of the recurrence and induction by doubling give
`s(n + 4·2ʳ) + s(n) = Tᵣ · s(n + 2·2ʳ)`. Each `Tᵣ` is 3 modulo 4, so it has a prime divisor `p ≡ 3 (mod 4)`. Shifting the index by an odd multiple of `4·2ʳ` negates the term modulo `p`. If the starting term is a square whose root is coprime to `p`, the shifted term cannot be a square since −1 is a quadratic nonresidue modulo `p`. [Cohn’s dyadic congruences](https://msp.org/pjm/1968/26-2/pjm-v26-n2-p03-p.pdf)

For the upper sequence, start at the squares at indices 0, 1 and 3, together with 81 at index −9 of the recurrence extended backwards. For the lower sequence the corresponding starting indices are −3, −1 and 9. Write the difference of indices as a power of two times an odd number. This picks the appropriate `Tᵣ` for each comparison. For roots 3 and 9 the comparisons have `r ≥ 1`, when 3 does not divide `Tᵣ`. A period of 12 modulo 8 excludes all remaining classes. The negative indices are used only inside the proof, represented by shifting an integer recurrence to natural indices.

## Quartic equations

The two diagonals together comprise exactly the natural `v` for which `x² − 5v² = ±44` has a natural witness. Substituting `v = y²` gives all solutions in nonnegative integers to the two quartics. For `x² = 5y⁴ + 44`, the sole pair `(x,y)` is `(7,1)`. For `x² = 5y⁴ − 44`, the pairs are `(6,2)`, `(19,3)` and `(181,9)`. These are Cohn’s cases (iii) and (v). [Diagonal characterization](DiagonalUnion.md) · [Cohn, p. 241](https://msp.org/pjm/1968/26-2/pjm-v26-n2-p03-p.pdf)

The declarations are `lucasFibonacciSum_isSquare_iff`, `lowerNeighbor_isSquare_iff` and `quartic_norm_forty_four_iff` in namespace `Arxiv.«2211.10788»`. The lower declaration uses `lowerNeighborAtAddTwo m`, so its square occurs at `m = 7`. Index 1 of the lower diagonal has value 3. Each proof uses only `propext`, `Classical.choice` and `Quot.sound`. Searches of DeepMind and OMA issues and pull requests and LTS solved records found no matching formalization. Codex assisted with the formalization. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [OMA search](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%222211.10788%22) · [LTS records](https://lefttosolve.com/api/solved) · [Notebook replay](../../README.md#replay)
