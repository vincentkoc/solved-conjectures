# Theta sum modulo four

**Checked result.** For every odd prime `p`, `S_mod_four` proves `S p ≡ (p : ℤ) - 1 [ZMOD 4]`. Consequently `S_ne_zero_of_three_mod_four` proves `S p ≠ 0` whenever `p.Prime` and `p % 4 = 3`. This is the pointwise congruence in Berndt, Bhat, Meyer, Xie and Zaharescu. The paper also states an asymptotic equidistribution result, beyond the scope of this file. [v1, Corollary 6.3](https://arxiv.org/pdf/2501.03234v1#page=16) · [v3, Proposition 7.1](https://arxiv.org/pdf/2501.03234v3#page=18)

**Upstream coverage is partial.** `Arxiv.«2501.03234».conjecture_1_1` requires `0 < S p` for every odd prime, including 3 and 5. The congruence determines the residue for every such prime. Its sign remains undetermined, and residue zero still permits the value zero. The proof imports the original sum, including both intervals and the rational floor. [Pinned declaration and definitions](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean#L41-L66)

**Proof.** Write `p = 2m + 1` and pair rows `h` and `p − h`. For each interior column `j`, primality gives `p ∤ hj`, so the two floor quotients add to `j − 1`. Using `(−1)^a ≡ 1 − 2a (mod 4)`, the paired summands contribute `2j`. Summing over columns gives `2m` modulo four per row pair, hence `2m² ≡ 2m = p − 1` overall.

**Preclaim check, 2026-11-28.** Searched open and closed DeepMind and OMA issues and PRs by paper ID, title, file path, declaration and mod-four wording, and checked the complete LTS solved feed. No matching Lean proof of this congruence surfaced. DeepMind’s related issue discusses row identities and finite computations. OMA already has reductions using the same floor reflection and a checked odd-harmonic-sum step. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5611) · [OMA harmonic bound](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7126) · [LTS solved records](https://lefttosolve.com/api/solved)

**Replay from the research worktree root.** Both public theorems print only `propext`, `Classical.choice` and `Quot.sound`.

```sh
proof="$PWD/research/arxiv/theta-sum/ArithmeticSumModFour.lean"
source ~/formal-math/env.sh
(cd ~/formal-math/fc && lake build 'FormalConjectures.Arxiv.«2501.03234».ArithmeticSumS' && lake env lean "$proof")
```
