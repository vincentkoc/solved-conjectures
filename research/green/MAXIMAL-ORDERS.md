# Green 33 · maximal cyclic orders at every size

For a set of `k` distinct residues containing zero, Graham and Sloane call the largest possible cyclic order `nγ(k)` when each residue must be the sum of two distinct elements, and `nδ(k)` when repetitions are allowed. Both normalized orders converge along **all** integer budgets:

```text
lim nγ(k)/k² = lim nδ(k)/k² = S,
S = sup { M/|A|² : A is a finite strict sum cover of Z/M },
7/18 ≤ S ≤ 1/2.
```

The supremum ranges over positive cyclic orders. Green 33 is equivalent to `S = 1/2`. Its value remains open. The theorem `graham_sloane_limits` treats both functions. The declaration `green_iff_orderConstant` uses the positive moduli, frequency quantifier, ordinary sumset equality and absolute tolerance of the pinned Green statement. [Lean proof](Green33MaximalOrders.lean) · [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

**Conventions.** Graham and Sloane start at `k=2` and set `nγ(2)=1` by convention. The Lean definition `grahamSloaneOrder` does the same at two and extends the functions below their original domain. An auxiliary optimization allows at most `k` labels and assigns zero when no positive modulus is feasible. For `k≥3`, the whole group of order `k` is a strict cover. A maximizing group therefore has at least `k` elements, so a cover can be padded to exactly `k` labels and translated to include zero. Translation shifts every sum by the same amount and preserves distinctness. [Graham–Sloane, §1](https://mathweb.ucsd.edu/~ronspubs/80_07_harmonious.pdf#page=1)

## Why every large budget works

Fix a strict cover of size `h` modulo `M`. For `s=h!M` and every `Q=sℓ+1`, replace each label by a progression of length `s+Q`. The two progressions from any distinct seed labels cover their entire sum layer modulo `Q²`. Their labels keep the chosen summands distinct. CRT gives a strict cover of order `MQ²` at budget `h(s+Q)`. These budgets have constant spacing `hs`. Choosing the grid point below a given budget gives the following inequality for `C=3hs` and every `K≥C`,

```text
M(K−C)² ≤ h² maxOrder(strict, K).
```

Consequently every strict seed density is a lower bound on the limiting inferior of the strict normalized maximum. The twelve labels modulo 56 in Haanpää’s table 4 give `56/12²=7/18`. Counting unordered distinct pairs gives the upper bound `1/2`. [Progression pair lemma](STRICT-COVER-LIFT.md) · [Haanpää, table 4](https://cs.uwaterloo.ca/journals/JIS/VOL7/Haanpaa/haanpaa.pdf#page=9)

For an ordinary seed of size `h` modulo `N`, the finite strictification theorem produces a strict cover at normalized size at most `(h+2⌊√h⌋+3)/√N`. By the definition of the supremum, this implies `N ≤ S(h+2⌊√h⌋+3)²`. For all ordinary seeds with `h≤K`, dividing by `K²` gives limiting superior at most `S`. Strict covers are ordinary covers, completing the two limits. [Ordinary-to-strict lift](STRICT-REDUCTION.md)

## Source comparison

Graham and Sloane identified the strict function with the largest size of a harmonious subgraph of the complete graph on `k` vertices. They asked in §15 whether its normalized limit exists and for stronger bounds on its value. The Lean theorem establishes the existence statement in their additive formulation. Bevan, Erskine and Lewis distinguish the lower and upper limits for directed circulants as degree grows at fixed diameter. Their Theorem 10(a) gives a diameter-two lower bound of `3/8`. Their Theorem 15 takes the diameter to infinity. Jia and Shen give a lower bound of `(1−ε)/3` in the related convention using at most two summands. The comparisons here identify the statements checked, without claiming priority. [Graham–Sloane, §15](https://mathweb.ucsd.edu/~ronspubs/80_07_harmonious.pdf#page=20) · [Bevan–Erskine–Lewis](https://arxiv.org/pdf/1506.04962) · [Jia–Shen](https://doi.org/10.1137/15M1013237)

The notebook replay compiles the two imported lift modules before this file. The twelve axiom reports use only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the proofs. [Replay instructions](../README.md#replay) · [DeepMind statement issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33) · [Open Math Agents](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%22Green33%22)
