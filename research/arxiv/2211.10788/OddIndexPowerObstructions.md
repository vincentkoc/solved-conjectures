# Prime powers on the odd Hosoya diagonals

For each of the 24 odd primes `p < 101`, neither Lucas–Fibonacci diagonal at any positive odd index is a pth power of an integer. The same certificates exclude **all integer solutions of `x² + 44 = 5y^(2p)`** for these exponents. The index and the base are unbounded. [Finite-field certificates](HosoyaOddIndexPowerSieve.lean) · [Exponent and Pell theorems](HosoyaOddIndexPowerObstructions.lean)

Write `Uₙ = Fₙ + Lₙ₊₁ = 3Fₙ + Fₙ₊₁` for the upper diagonal and `Dₙ = Fₙ + Lₙ₋₁ = 4Fₙ − Fₙ₊₁` for the lower one at positive indices. The pinned definition of `lucasFibonacciSum n` is `2Fₙ + Fₙ₊₂`. Its open question asks whether infinitely many distinct prime values occur on the upper diagonal. The present result restricts proper powers among possible composite values. The earlier exponent obstruction concerned the product of both neighbors at a common index. [Pinned declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Ching et al.](https://arxiv.org/abs/2211.10788) · [Neighbor product](SplitPrimeExponentBounds.md)

## The odd-index sieve

For a prime modulus q with p dividing q−1, a pth power is either zero modulo q or has `u^((q−1)/p) = 1` in the field. Each row supplies a return time T of the Fibonacci pair to (0,1), a divisor d of both T and 2p, and a list of allowed residues modulo d. Lean checks both diagonal values at every odd position in a full cycle. It then checks that every odd residue modulo 2p fails at least one row for each diagonal. A return time suffices because the recurrence repeats from the same pair.

For fifth powers, q = 11 allows only index 5 modulo 10 on either diagonal. Modulo 31 the upper diagonal allows only 3, 7, 9 modulo 10, and the lower allows only 1, 3, 7. Neither list contains 5. Across all exponents the proof uses 32 rows. An independent enumeration of the actual power residues checked 8,030 Fibonacci positions across the listed cycles. The declaration `odd_index_not_small_prime_power` accepts an arbitrary integer base. [Sieve and row data](HosoyaOddIndexPowerSieve.lean)

If an odd-index term equals `t^k` with natural base t, every prime divisor of k is at least 101 except for the square exponent at upper indices 1 and 3 (values 4 and 9) and lower index 9 (value 81). The lower declaration uses the notebook counter m at physical index m+2. The separate initial lower term is 3. [Square classification](SquareValues.md) · [Upper and lower exponent theorems](HosoyaOddIndexPowerObstructions.lean)

## From indices to the negative Pell equation

Suppose `x² + 44 = 5y^(2p)` and put `b = |y|^p`. Completeness for the two Pell orbits places b on at least one diagonal. The sieve forces its index to be even. At that index the Fibonacci norm identity supplies an integer z with `z² = 5b² + 44`. Consequently `z² − x² = 88`. The two square equations together force b = 5. For example, factoring `(|z|−|x|)(|z|+|x|) = 88` leaves the even factor pairs (2,44) and (4,22), and only the second gives an integral b. No pth power is 5 for p ≥ 3. This proves `negative_pell_prime_power_obstruction` without a Diophantine solver. [Pell completeness](DiagonalUnion.md) · [Lean proof](HosoyaOddIndexPowerObstructions.lean)

For p = 5, Song’s Theorem 3.2 classifies the positive branch `x² = 5Z⁵ + 44` at positive Z. Under this explicit hypothesis, `fifth_powers_of_positive_quintic` proves that `t⁵` occurs on either diagonal exactly when t = 1, realized by the upper term at index zero. On the opposite branch the unconditional theorem above handles every square argument `Z = y²`, which is all the diagonal application requires. Song’s Theorem 4.2 also handles nonsquare Z. The positive-branch hypothesis remains external to the Lean proof. [Song, Theorems 3.2 and 4.2](https://arxiv.org/pdf/2611.19995#page=4)

Lean 4.33.1 rebuilt and independently kernel-replayed five notebook modules. All 17 named axiom reports contain only standard Lean axioms from `propext`, `Classical.choice` and `Quot.sound`. [Notebook replay](../../README.md#replay)
