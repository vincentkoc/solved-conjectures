# Cubes on both Hosoya diagonals

The upper sequence `Uₙ = Fₙ + Lₙ₊₁` starts at index zero. On the lower sequence `Dₙ = Fₙ + Lₙ₋₁`, the first positive index gives `D₁=3`. The only cube values are `U₀=1` and `D₁₂=343=7³`, by the published integral-point classification of Bennett and Ghadermarzi. Lean proves the deduction with the completeness of their row for `k=1100` as an explicit hypothesis. A separate, unconditional Lean theorem characterizes every cube on either diagonal by two irreducible sextic Thue equations. The original infinitude of prime upper values remains open. [Pinned upper sequence and question](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Ching et al.](https://arxiv.org/abs/2211.10788) · [Cube proofs](LucasFibonacciEvenCubes.lean)

## The published point classification

The exact criterion for the union of the two diagonals gives `x² = 5t⁶ ± 44` for a cube `t³`. The minus sign is impossible modulo 7. The plus sign gives an integral point `(X,Y)=(5t²,5x)` on `Y²=X³+1100`. Page 11 of the authors’ positive-k table gives the eight points `(−10,±10), (5,±35), (14,±62), (245,±3835)`. The two admissible X-coordinates give t = 1 and 7. The upper and lower sequences share only 5. Direct evaluation locates the two witnesses, and strict growth on the upper sequence and on the lower tail starting at index 2 establishes uniqueness of their indices. [Diagonal union](LucasFibonacciDiagonalUnion.lean) · [Bennett and Ghadermarzi, *Mordell’s equation: a classical approach*](https://doi.org/10.1112/S1461157015000182) · [Authors’ positive-k table, p. 11](https://personal.math.ubc.ca/~bennett/0-10%5E6n.pdf#page=11)

`Mordell1100RowComplete` states that every integral point has X-coordinate −10, 5, 14 or 245. The declarations `cube_roots_of_mordell_row` and `cube_indices_of_mordell_row` take this proposition as an argument. The latter uses `lowerNeighborAtAddTwo m`, so m = 10 means actual lower index 12. [Lean declarations](LucasFibonacciEvenCubes.lean)

## The two Thue equations

Write `(a+b√11)⁶ = R + 2H√11`. The unconditional theorem `either_diagonal_cube_iff_sextics` says that `t³` occurs on either diagonal if and only if there are integers a,b with `t=|a²−11b²|` satisfying one of

```text
R − 7H = 1             −11R − 73H = 1
R = a⁶ + 165a⁴b² + 1815a²b⁴ + 1331b⁶
H = 3a⁵b + 110a³b³ + 363ab⁵.
```

The pairs `(1,0)` and `(2,−1)` give the two known roots, respectively. After setting b=1 and translating a by 1, both polynomials are primitive and Eisenstein at 5. Their translated constant terms are −20 and −71180. [Irreducibility and equivalence](LucasFibonacciEvenCubes.lean)

In the ring ℤ[√11], the absolute norm is Euclidean. The proof covers the closed half-by-half square by subdividing it into 32 by 32 cells and testing six lattice points against rational bounds on each coordinate square. Reflection and translation extend the covering to all rational coordinate pairs. The fundamental norm-one unit is ε=10+3√11 and norm −1 is impossible modulo 11. [Norm-Euclidean covering and units](HosoyaRealEleven.lean)

Choose the sign of x so that `x ≡ 3 (mod 5)`. The element `x+2√11` is divisible by `4+√11`, of norm 5. The quotient and its conjugate are coprime because any common divisor divides the original trace and norm, which are relatively prime integers. Their product is t⁶, so the quotient is a sixth power times a unit. Absorbing sixth powers of ε leaves the six twists `(7−2√11)εʳ` for 0 ≤ r < 6. The √11 coefficient of a twisted sixth power must be ±2. Reduction modulo 4 removes r = 1, 3, 5. Modulo 9 removes r = 4, and modulo 7 removes the sign +2. The two surviving twists give the displayed equations. Conversely, taking norms reconstructs x² = 5t⁶+44, so each solution gives an actual diagonal value. Song uses a related real quadratic descent for fifth powers in the upper sequence’s tail. [Sixth-power descent](LucasFibonacciEvenCubes.lean) · [Song, *Two Quintic Diophantine Equations and Fifth Powers in Fibonacci Sums at Distance Five*](https://arxiv.org/abs/2611.19995)

## Verification and related work

Lean 4.33.1 compiled the pinned upstream file and four notebook modules from fresh output. Independent kernel replay passed for each notebook module. All 16 requested axiom reports used only `propext`, `Classical.choice` and `Quot.sound`. [Replay instructions](../../README.md#replay)

Searches of open and closed DeepMind and OMA issues and pull requests and 4,360 LTS solved records located the canonical prime-values question and statement PR. The earlier notebook result excludes cubes at positive odd indices by a separate descent in the imaginary quadratic field. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/8156) · [OMA](https://github.com/lefttosolve2/open-math-agents) · [LTS records](https://lefttosolve.com/api/solved) · [Odd-index cubes](OddIndexCubes.md)
