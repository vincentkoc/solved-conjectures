# Green 33 · a full progression of cyclic orders

There is a fixed positive integer **D** such that every sufficiently large multiple of **D** admits a strict two-basis with normalized size arbitrarily close to **18/√130 ≈ 1.578704**. The threshold may depend on the tolerance. For every ε > 0, at least ⌊X/D⌋ − Cε of the orders through X admit such a basis, giving lower natural density at least 1/D. The divisor arises from the finite seed and the slope gaps. The earlier quartic construction supplied a subsequence inside any prescribed divisibility class. [Lean proof](Green33DenseModulus.lean) · [Quartic seed and its Erskine–Lewis source](QUARTIC-SEED.md) · [Previous divisible-order lift](DIVISIBLE-ORDERS.md)

The general result starts with any strict k-label cover modulo M. It produces positive L and a constant K, fixed before n or ε is chosen. For every sufficiently large n divisible by L there is a strict cover B modulo Mn satisfying

```text
|B| ≤ k (⌊√n⌋ + K (⌊√⌊√n⌋⌋ + 1)).
```

Padding gives covers whose normalized size tends to k/√M along the entire progression of multiples of D = ML. The theorem `green_iff_dense_progressions` consequently equates the pinned Green 33 with the following condition. For each ε > 0 there is a D such that every sufficiently large multiple of D has a strict cover within ε of √2. Here D may depend on ε because the seed may change. Attainment of √2 remains open. [Pinned ordinary conjecture](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Finite strict-seed equivalence](STRICT-REDUCTION.md)

## Fitting a rectangle to the order

Choose distinct slopes i with each positive gap d = j−i dividing i+1 and L. Set r = ⌊√n⌋. Choose a multiple c of L a bounded distance above r so that c(c−1) ≥ n. Round the square root of c(c−1)−n up to a multiple z of L. The sides p = c+z and q = c−1−z satisfy

```text
pq = c(c−1) − z² − z,     p ≡ 0 (mod L),     q ≡ −1 (mod L).
```

The starting excess is O_L(√n), so z, the side difference, and the remaining deficit δ = n−pq are all O_L(n^{1/4}+1). The proof bounds all three for every n, then uses positivity of q for sufficiently large n. This near-square argument is related to the elementary fourth-root construction in the literature on almost squares. [Chan, *Finding Almost Squares*, theorem 1.3](https://arxiv.org/abs/math/0502199)

For a pair of slopes write wᵢ = 1+ip. On the rectangle of order pq the carry is h = (i(p−q)+1)/d, an integer by the gap conditions. Splitting the low digit at that carry gives representatives t,u in [0,p+h). For a target x in [0,n), write x = wᵢt+wⱼu+pq e. The winding satisfies |e| ≤ 8(H+1), where H bounds the slopes. Since n and pq are divisible by d, set v = δ/d. The identity jwᵢ−iwⱼ = d gives the exact correction

```text
x = wᵢ(t−jev) + wⱼ(u+iev) + n e.
```

Thus every pair works in the actual modulus after extending both ends of each coefficient interval by O_H,L(n^{1/4}+1). Distinct seed labels keep the resulting cyclic representatives distinct. The finite count in `quartic_count` follows by mapping the large integers l through X/D to the good orders Dl. [Formal integer identities and counts](Green33DenseModulus.lean)

## Scope and verification

The degree-17 circulant underlying the 18-label seed is tabulated by Lewis, who credits the finite extremal search to Erskine and Lewis. The present theorem uses its strict-sum certificate, the earlier slope construction, and a perturbation of the cyclic order. Bevan–Erskine–Lewis give a separate infinite cyclic construction in theorem 10(a). Jia–Shen study maximal cyclic orders for size budgets in the convention of at most two summands. The result above prescribes every sufficiently large order on one seed-dependent progression. [Lewis, table 5](https://arxiv.org/pdf/1506.02844#page=14) · [Bevan–Erskine–Lewis](https://arxiv.org/pdf/1506.04962) · [Jia–Shen](https://doi.org/10.1137/15M1013237)

The Lean 4.33.1 audit covers all thirteen public theorems, including the signed correction, finite bound, frequency equivalence, and positive-density count. The independent replay includes the six notebook dependencies. The axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`. Codex assisted with the proof. [Replay](../README.md#replay) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33) · [Open Math Agents](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%22strict+sum+cover%22)
