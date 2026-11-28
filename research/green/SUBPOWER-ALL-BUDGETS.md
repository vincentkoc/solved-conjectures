# Green 33 and Erdős 840 · subpower multiplicity at every budget

For every fixed positive integer `h`, impose the restriction `R(A)^h ≤ M` on a cyclic basis of order `M`, where `R(A)` is the maximum **ordered** representation count, including equal summands. With at most `K` elements, the largest admissible order divided by `K²` tends to the same constant as in the unrestricted Graham–Sloane problem. This holds for both ordinary and distinct-summand covers. One family indexed by **every size budget** attains that limit while satisfying every fixed power restriction eventually. This result is unconditional. [Budget theorems](Green33SubpowerBudgets.lean) · [Graham–Sloane conventions and unrestricted limit](MAXIMAL-ORDERS.md)

Under Green 33 there are sets `S_n ⊆ [1,n]` witnessing **Erdős 840 at √2**, with all three properties

```text
|S_n| / √n → √2
|S_n + S_n| / binom(|S_n|,2) → 1
for each positive integer h, eventually every integer sum has ordered count r with r^h ≤ n.
```

All limits run over the full sequence of integer lengths. The first two limits use the literal upstream predicate `Erdos840.IsQuasiSidonConstant`. The additional bound applies to the same sets. The value of the supremum in Erdős 840 and the existence assertion in Green 33 remain open. [Interval theorem and predicate check](Green33SubpowerIntervals.lean) · [Pinned Erdős 840](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/840.lean) · [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

## A finite construction with a composite radix

Start with a finite strict seed of size `k` and order `M`, and put `s = k!`. For every `q = sl+1` with `q ≥ 6` and `s < q`, and every dimension `d`, the construction gives a strict basis at order `N = M(q²)^d` with

```text
|B| ≤ k(q+s)^d
R(B) ≤ k² [32(4k+7)]^d (q+s).
```

The earlier digit construction used the same prime for the radix and the quadratic correction. Here Bertrand's postulate supplies a separate prime `q/2 < p ≤ q`. The digit is `(s+iq)t + q(a² mod p)` for label `i`, previous parameter `a` and present parameter `t`. Since `gcd(s,q)=1`, reduction of the sum of two blocks still recovers the sum of the parameters modulo `q`. For equal labels the *next* block also supplies the sum of the preceding squares modulo `p`. The two parameters, each below `q+s ≤ 4p`, can then be recovered from their exact sum, square sum, residue order and the first parameter's quotient by `p`. The extra two choices of quotient account for the change from 16 to 32. Distinct-label coverage continues to use the progression modulo `q²`. [General digit proof](Green33QuadraticRadix.lean) · [Prime-radix bound](SUBPOWER-REPRESENTATIONS.md)

## From the grid to every budget

For fixed `h`, take `d=h+1`. The peak grows at most linearly in `q`, so its `h`th power is eventually bounded by the order. Consecutive values of `q` differ by `s`. For a budget between two consecutive bounds `k(q+s)^d`, use the smaller one. The resulting order divided by the square of the larger bound tends to `M/k²`, the original seed density. The lemma `seed_all_budgets` gives every density strictly below it at every sufficiently large budget. [Lean proof](Green33SubpowerBudgets.lean)

Take the supremum over finite strict seeds and let the exponent grow slowly with the budget. The theorem `all_budget_family` gives one strict family with normalized order tending to that supremum. The theorem `capped_order_limit` compares it with the unrestricted maximum and handles both coverage conventions. The certified 18-point strict seed modulo 130 gives the lower bound `130/18² = 65/162`. The upper bound is `1/2`, with equality if and only if Green 33 holds. Here `cappedOrder` uses an **at-most** budget and value zero for an empty feasible set. Arbitrary padding can change multiplicity, so the formal capped theorem uses this budget convention throughout. [Capped maxima](Green33SubpowerBudgets.lean) · [Order-130 seed](Green33QuarticSeed.lean) · [Finite-density characterization](MAXIMAL-ORDERS.md) · [Graham and Sloane, §15](https://mathweb.ucsd.edu/~ronspubs/80_07_harmonious.pdf#page=20)

## Transfer to integer intervals

At length `n` choose budget `⌊√(2n)⌋`. Under Green 33 the cyclic order `M` satisfies `M/n → 1` and fits in the interval by the strict unordered-pair count. Represent each cyclic point by its least residue plus one. The integer copy retains the cardinality and has at least `M` sums. The counting lower bound for strict bases and the size budget squeeze its size divided by `√n` to `√2`. Reduction sends every ordered pair of integer representatives with sum `t` injectively to the cyclic fiber at `t−2`. This preserves the required upper bound without adding points to the copy. [Finite fiber injection and interval limit](Green33SubpowerIntervals.lean)

Erdős and Freud obtained the unconditional lower constant `2/√3`, and Pikhurko proved an unconditional upper constant of approximately `1.863`. Open Math Agents contributions formalize the Erdős–Freud lower bound. The conditional `√2` transfer here strengthens the notebook's earlier interval result by bounding the multiplicity of every sum. [Erdős–Freud](https://www.sciencedirect.com/science/article/pii/0022314X9190083N) · [Pikhurko](https://pikhurko.github.io/E/Pikhurko06dm.pdf) · [OMA proof](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1478) · [Shorter OMA proof](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/11577) · [DeepMind proof links](https://github.com/google-deepmind/formal-conjectures/pull/8281) · [Previous interval result](QUASI-SIDON-INTERVALS.md)

The DeepMind and Open Math Agents tracker searches found no matching subpower interval or budget theorem. Left to Solve's entries were checked for the two pinned problems. The eleven local modules in the import closure were rebuilt from clean sources with Lean 4.33.1 and replayed separately using the kernel checker. The 24 axiom prints in the five affected modules report only `propext`, `Classical.choice` and `Quot.sound`. [Green 33 tracker](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Green 33 at Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33) · [Erdős 840 at Left to Solve](https://lefttosolve.com/api/problems/Erdos840.erdos_840) · [OMA search](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%22quasi-Sidon%22+%22subpower%22)
