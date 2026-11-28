# Green 33 · all large multiples of the seed order

Every sufficiently large multiple of 130 has a set in which each residue is the sum of two distinct members and whose size, divided by the square root of the modulus, is within any prescribed ε > 0 of **18/√130 ≈ 1.578704**. For each ε the number of qualifying positive orders at most X is at least **⌊X/130⌋ − Cε**, so their lower natural density is at least **1/130**. The finite seed is the affine copy of the degree-17 circulant in Lewis's table 5. The preceding progression theorem supplied a divisor depending on that seed. Here the divisor is exactly 130. [Lean proof](Green33SeedMultiples.lean) · [Finite seed and attribution](QUARTIC-SEED.md) · [Previous progression theorem](DENSE-MODULUS-LIFT.md) · [Lewis, table 5](https://arxiv.org/pdf/1506.02844#page=14)

## General theorem

Suppose A has k elements in the cyclic group of order M and each residue is a sum of two distinct elements of A. There is an integer K depending only on A such that for **every sufficiently large positive n**, the cyclic group of order Mn has a strict cover of size at most

```text
k (⌊√n⌋ + K (⌊√⌊√n⌋⌋ + 1)).
```

The theorem `seed_all_cofactors` gives this finite bound. Padding preserves the distinct witnesses and yields `seed_ratio`, with normalized size within ε of k/√M on every sufficiently large multiple of M. Specializing gives `quartic_multiples` and `quartic_count`. The pinned conjecture asks for infinitely many positive orders with ordinary sumset equality and normalized size within every positive tolerance of √2. The coefficient proved unconditionally here is 18/√130. [Statements and proof](Green33SeedMultiples.lean) · [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

## Removing the cofactor restriction

Choose the finite set of integer slopes from the preceding lift. For each ordered pair of slopes i < j, the gap d = j − i divides a common positive L and also divides i + 1. For a target cofactor n choose the low digit c = 1 + (−n mod L), between 1 and L. Prescribe p ≡ c − 1 and q ≡ −n − c modulo cL. Then c divides p + 1, L divides both q + 1 and p − q − c, and cL divides n − pq. The last assertion follows from the identity n − (c − 1)(−n − c) = c(n + c − 1). These identities hold even when n shares prime factors with L.

One fixed grid of modulus T = L! L realizes all the required classes. To obtain factors near √n, take the next integers y and x in the assigned classes with ⌊√n⌋ < y < x and both gaps at most T. With B = xy − n, let z be the first multiple of T strictly above ⌊√B⌋. Put p = x + z and q = y − z. Both factors retain their classes. The identity n − pq = z² + (x − y)z − B bounds the product deficit and side difference by a constant times n^(1/4) + 1. The constant is uniform over the residue classes. Chan's Theorem 1.3 gives related near-square estimates for unrestricted factors. [Chan, *Finding almost squares*](https://arxiv.org/pdf/math/0502199)

Use the two weights c + ip and c + jp. The divisibility above makes h = (i(p − q) + c)/d integral. Writing a target first as ca + pb, with 0 ≤ a < p, gives two carry cases. Both put the initial coefficients t,u in [0,p + h) and leave a residual term pq e. The winding e is bounded in absolute value by a constant depending only on the slopes. Write n − pq = cdv. Replacing (t,u) by (t − jev,u + iev) changes the residual modulus from pq to n because j(c + ip) − i(c + jp) = cd. The resulting common coefficient interval is longer by at most a constant times n^(1/4) + 1. The two labels are still distinct modulo M, including when M and n share factors. [Weighted pair and assembly](Green33SeedMultiples.lean) · [Cyclic assembly lemma](Green33DenseModulus.lean)

## Verification and related work

The independent Lean 4.33.1 replay builds the seven notebook dependencies and this module from source. All nine public theorems print only `propext`, `Classical.choice`, and `Quot.sound`. Bevan–Erskine–Lewis give an infinite construction in theorem 10(a). Jia–Shen bound the largest admitted cyclic order at each sufficiently large size budget. The claim here fixes the seed order and allows all large cofactors. Codex assisted with the formalization. [Replay](../README.md#replay) · [Bevan–Erskine–Lewis](https://arxiv.org/pdf/1506.04962) · [Jia–Shen](https://doi.org/10.1137/15M1013237) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33) · [Open Math Agents](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%22strict+sum+cover%22)
