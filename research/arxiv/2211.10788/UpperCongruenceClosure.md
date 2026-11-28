# Which Lucas–Fibonacci values survive every congruence test?

Write `U(n) = Fₙ + Lₙ₊₁` for n ≥ 0 and `V(k) = Fₖ + Lₖ₋₁` for k ≥ 1. A natural number y occurs modulo every positive integer among the U(n) exactly when **y is an upper value or an odd-index lower value**. The two ranges meet only at 5. In particular 3 and 31 are prime, never equal U(n) for n ≥ 0, and nevertheless occur among its residues for every modulus. The pinned declaration asks whether infinitely many primes actually equal U(n). That question remains open. [Lean proof](LucasFibonacciCongruenceClosure.lean) · [Pinned definition and question](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Ching et al.](https://arxiv.org/abs/2211.10788)

## One modulus suffices

For y ≥ 3 put A = 5y² + 44, B = 5y² − 44 and M = 11(AB)². For y < 3 take M = 11. The following tests are equivalent.

1. Every positive modulus admits an index n ≥ 0 with U(n) ≡ y.
2. For this single M there is an index 0 ≤ n < M² with U(n) ≡ y modulo M.
3. Some U(n) equals y, or some V(2a+1) equals y.

The bound M² counts pairs of Fibonacci residues. The step (u,v) ↦ (v,u+v) is invertible, so every modular orbit is periodic from its first term. This also means every negative-index upper term recurs at a nonnegative index modulo M. At the negative odd index −k, the bilateral recurrence gives U(−k) = V(k). The prime examples are V(1) = 3 and V(7) = 31. Lipton et al. discuss the distinction between one-sided and bilateral recurrences in the Skolem local-global problem. [Lipton et al., §1](https://people.mpi-sws.org/~jnieuwve/Papers/OnTheSkolemProblemAndTheSkolemConjecture.pdf)

For the converse, take an upper term congruent to y modulo M. Its Pell witness gives a square congruent either to A modulo A² or to B modulo B². For a positive integer D, the congruence x² ≡ D modulo D² forces D to be a square. Write x² = Dc. Then c ≡ 1 modulo D, so D and c are coprime factors of a square. The resulting integer Pell witness places y on one of the two diagonals. [Pooled Pell criterion](DiagonalUnion.md) · [Square and orbit lemmas](LucasFibonacciCongruenceClosure.lean)

To distinguish the lower indices, U(n) ≡ 4ⁿ modulo 11, a nonzero square. For even k ≥ 2 the bilateral term U(−k) equals −V(k), so −V(k) is also a nonzero square modulo 11. As −1 is a nonsquare modulo 11, V(k) cannot be a local upper value. For y = 0, 1, 2 the same modulus leaves only 1 = U(0).

Lean 4.33.1 rebuilt three notebook modules and independently replayed them in the kernel. All 13 named axiom reports used only `propext`, `Classical.choice` and `Quot.sound`. Independent integer arithmetic compared the Pell and modulo-11 classification with generated sequence values for every y from 0 through 1,000,000, exhausted the 256 modular orbits for 1 ≤ M ≤ 256, and tested the square criterion for 1 ≤ D ≤ 80. [Notebook replay](../../README.md#replay)
