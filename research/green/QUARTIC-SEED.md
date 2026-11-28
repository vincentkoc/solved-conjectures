# Green 33 · eighteen strict labels modulo 130

The normalized size of a cyclic two-basis can tend to **18/√130 ≈ 1.578704** along arbitrarily large multiples of any prescribed positive integer. Every residue in these bases has a representation by two distinct elements. This lowers the notebook's previous constructive constant of √(18/7) ≈ 1.603567. Green's target of √2 remains open. [Lean proof](Green33QuarticSeed.lean) · [Previous construction](STRICT-COVER-LIFT.md) · [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

## The finite seed

Take the following residues modulo 130.

```text
0, 2, 8, 13, 14, 32, 36, 39, 56, 65, 74, 91, 94, 98, 116, 117, 122, 128
```

The affine map `x ↦ 9x+65` takes this set to zero together with the connection set of the degree-17 circulant of order 130 in Lewis's table 5. Lewis credits the diameter-two extremal searches to Erskine and Lewis. Their graph permits two traversals of the same generator. The theorem `seed_strict` checks the extra distinctness needed here, and `lewis_seed` checks the affine identification. This uses a published finite graph. [Lewis, table 5 and §6](https://arxiv.org/pdf/1506.02844#page=14)

The labels have a character description. Write **χ** for the multiplicative character from the nonzero elements of **F₁₃** to **F₅** determined by χ(2) = 3, with χ(0) = 0. The even labels are the residues `2b` for which `b mod 5 = χ(b mod 13)`. The odd labels are all five odd multiples of 13. In CRT coordinates using one half of the residue in each odd field, the even layer is the graph of χ and the odd layer is the vertical axis.

Every odd target is one graph point plus one axis point. Every even target with first field coordinate zero is the sum of two distinct axis points. For the remaining even targets it suffices to check first coordinate one. The six distinct pairs in that row are (0,1), (2,12), (3,11), (4,10), (5,9), (6,8). Their color sums are 1, 2, 3, 3, 4, 0 respectively. Scaling a pair by any nonzero field element scales both its row and its color, so this one check covers all twelve nonzero rows. The general theorem `index_two_cover` applies this argument to other finite fields and multiplicative characters satisfying the same row condition. [Character and finite certificates](Green33QuarticSeed.lean)

## Passage to arbitrarily large moduli

For every positive divisor `D`, the rectangular lift gives constants `s>0` and `C`. At each sufficiently large width `p=sℓ`, it produces a strict cover of order `130p(p−1)` divisible by `D`, using at most `18(p+C)` labels. Padding to exactly that cardinality preserves the distinct witnesses. Dividing by the square root of the order gives the claimed limit. The theorem `frequently_cyclic_basis` has the positive moduli, ordinary sumset equality, frequency at infinity, and absolute tolerance of the pinned conjecture, with its target constant replaced by 18/√130. [Rectangular lift](DIVISIBLE-ORDERS.md) · [Bevan–Erskine–Lewis, theorem 10(a) and corollary 18](https://arxiv.org/pdf/1506.04962)

The finite seed has zero missing strict sums. Its charged density is therefore **130/18² = 65/162**. This improves the notebook's lower bound on the common Graham–Sloane order constant by exactly **1/81**, from 7/18 to 65/162. Its upper bound remains 1/2. Haanpää computed minimum strict covers of groups through order 90. Neither that range nor the present certificate settles the minimum strict size at order 130. [Finite charged-density certificate](APPROXIMATE-COVERS.md) · [Maximal order limit](MAXIMAL-ORDERS.md) · [Haanpää, §5](https://cs.uwaterloo.ca/journals/JIS/VOL7/Haanpaa/haanpaa.pdf#page=7)

The Lean 4.33.1 proof includes eleven axiom reports. The independent replay uses only `propext`, `Classical.choice`, and `Quot.sound`. The live DeepMind issue and statement PR, Left to Solve, and Open Math Agents were checked for the same declaration and construction. Codex assisted with the formalization. [Notebook replay](../README.md#replay) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33) · [Open Math Agents search](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%22strict+sum+cover%22)
