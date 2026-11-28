# Green 33 · three progressions on every large modulus

For every ε > 0 and every sufficiently large positive integer N, there is a union A of three arithmetic progressions modulo N such that every residue is the sum of two **distinct** members of A and `||A|/√N − √3| < ε`. This includes every sufficiently large prime. The coefficient **√3 is optimal among unions of three progressions**, even for ordinary two-bases. [Lean proof](Green33AllModulusHexagon.lean) · [Lower bound for families of progressions](PIECE-OBSTRUCTION.md)

Green 33 asks for an ordinary two-basis at coefficient √2 on infinitely many orders. The theorem `all_moduli` includes the pinned equality `A + A = Finset.univ`. Its coefficient is √3 and its quantifier covers all large orders. The notebook's smaller coefficient `18/√130` applies on all large multiples of 130. The unrestricted √2 question remains open. [Pinned declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [All large multiples of 130](ALL-SEED-MULTIPLES.md)

## The three progressions

Take `P = ⌊√⌊N/3⌋⌋` and `R = P + 120(⌊√P⌋+1)`. For every `N ≥ 192`, the theorem `three_arms` supplies a positive integer p. For each of the three differences `−p, 2p+1, −(p+1)`, take all multiples of that difference with coefficients from −1 through R+1. Together they form a strict two-basis of size at most `3(R+3) = √(3N) + O(N^(1/4))`. The radius allowance is uniform and the finite proof also works with the smaller radius below. [Construction](Green33AllModulusHexagon.lean)

The homomorphism from the integer plane to residues modulo N sends `(x,y)` to `p x − (2p+1)y`. It maps `(−2,−1)` to 1. In the hexagon given by `max(|x|,|y|,|x−y|) ≤ r`, every integer point is the sum of points on two of the rays `(−i,0), (0,−i), (i,i)`, each with parameter in `[0,r]`. For example, if y is the largest of 0, x and y, use `(−(y−x),0) + (y,y)`. If two projected summands coincide at a multiple td, replace their sum by `(t−1)d + (t+1)d`. The endpoints are present and `2d ≠ 0` modulo N for these three differences. [Proof](Green33AllModulusHexagon.lean)

## Fitting every order

The ideal hexagonal periods `p(2,1), p(1,2)` have determinant `3p²`. To achieve determinant exactly N, put

```text
L = 3P² + 9P − N,       h = ⌊√⌊L/3⌋⌋,
p = P+h,                 q = 3P+9−3h,          e = N−pq,
u = 4p+2+2e−q,           v = 2p+e.
```

The integer periods `(2p+1,p)` and `(u,v)` lie in the kernel and their determinant is `pq+e=N`. Since `h ≤ 2(⌊√P⌋+1)` and `|e| ≤ 15h+2`, the new periods differ from the ideal ones by `O(√P+1)` in each coordinate. In a fundamental parallelogram for the new periods, choose a corner using the ideal hexagonal tiling. The two remaining period coefficients have absolute values at most one. Thus every residue has an integer representative of hexagonal radius at most `p+1+|u−p|+|v−2p| ≤ R`. The declarations are `hex_parameters` and `hex_representative`. [Proof](Green33AllModulusHexagon.lean)

Hexagonal meshes and degree-six geometric circulants provide the classical geometry. Thomson and Zhou discuss the extremal orders `3k²+3k+1`; Monakhova describes related parameterized circulant families. Chan studies products of near-square factors. The proof here uses explicit perturbed periods for each prescribed N and then projects the three rays to a two-basis. [Thomson and Zhou](https://arxiv.org/abs/1205.5877) · [Monakhova](https://doi.org/10.17223/20710410/54/6) · [Chan](https://arxiv.org/abs/math/0502199)

## Matching lower bound and replay

The finite theorem `three_progression_lower` gives `3N ≤ k²+18k` for *any* ordinary basis of size k that is a union of three progressions. They can overlap, wrap and have different lengths. It follows that `√(3N) ≤ k+9`. Together with the construction this proves the claimed limit on every large order. [Finite lower bound](Green33AllModulusHexagon.lean) · [Underlying counting inequality](Green33PieceObstruction.lean)

The independent Lean 4.33.1 replay builds the three notebook dependencies and this module from source. All five public theorems use only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the formalization. [Replay](../README.md#replay) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33) · [Open Math Agents search](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%22three+progressions%22+%22basis%22)
