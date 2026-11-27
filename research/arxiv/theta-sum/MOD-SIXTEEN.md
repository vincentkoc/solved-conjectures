# The theta sum modulo sixteen for primes congruent to one modulo eight

Let `p ≡ 1 (mod 8)` be prime. Let `Q` be the product modulo `p` of the odd integers in `{1, 3, …, p−2}` that are quadratic nonresidues. For the sum `S` defined by Berndt, Bhat, Meyer, Xie and Zaharescu, the product determines the residue completely. [Lean proof](ThetaNonresidueModSixteen.lean) · [Pinned definition of S and positivity conjecture](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean#L36-L64)

| Product modulo `p` | `S(p) mod 16` | Examples `(p, S(p))` |
| --- | --- | --- |
| `−1` | `8` | `(17, 24)`, `(73, 200)` |
| `+1` | `0` | `(41, 80)`, `(89, 192)` |

These are the only two values of `Q`. Together with the mod-eight result, any odd prime with `S(p) = 0` must satisfy both `p ≡ 1 (mod 8)` and `Q = 1`. The example at 41 shows why the second condition is only necessary. The congruence leaves positivity and the frequency of each product sign open. [Earlier mod-eight classification](GAUSS-FACTORIAL.md) · [Paper, Proposition 7.1](https://arxiv.org/html/2501.03234v3#S7)

## Proof

Write `p = 8k+1`, `m = 4k`, and let `O` be the odd representatives. For a unit `x`, write `L(x)` for the odd representative of `{x,−x}` and `s(x)` for the sign satisfying `x = s(x)L(x)` in the field. Over the unordered pairs of distinct elements of `O`, let `n` count the pairs with `s(ab) = −1`. The odd-representative identity gives `S(p) = 2 Σₐ,ᵦ s(ab)`. The diagonal sums to zero because multiplication by a square root of `−1`, followed by `L`, permutes `O` and reverses each diagonal sign. Thus

```text
S(p) = 4 [m(m−1)/2 − 2n] ≡ 8(k+n) (mod 16).
```

Let `P` be the product of all elements of `O`, `R` the product of its squares (elements of `O` that are squares in the field), and `Z` the product of `L(ab)` over unordered distinct pairs. For each `c ∈ O`, the equation `L(ab) = c` has `m` ordered solutions. For fixed `a` there is one choice of `b`. If `c` is square, then `c` and `−c` are square and each has one odd root, giving two diagonal solutions. A nonsquare has none. Consequently the multiplicity of `c` in `Z` is `m/2−1` for a square and `m/2` otherwise. Hence `ZR = P^(m/2)`.

Each vertex belongs to `m−1` unordered pairs, so their ordinary product is `P^(m−1) = (−1)^n Z`. Using `RQ = P` now gives `(−1)^n Q = P^(m/2)`. Wilson's theorem, pairing each element of `O` with its negative and using that `m` is even, gives `P² = −1`. Thus `Q = (−1)^(k+n)`, as required.

## Scope and replay

The public theorem `ThetaSixteen.S_mod_sixteen` uses the pinned integer sum directly, with `[Fact p.Prime]` and `p % 8 = 1`. The finite and harmonic reductions in OMA and the row-discrepancy reduction in DeepMind address different parts of positivity. Searches across the live DeepMind and OMA issues and PRs and the LTS solved records on 2026-11-28 found no matching modulo-sixteen classification. [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA reductions](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7053) · [LTS solved records](https://lefttosolve.com/api/solved)

The notebook replay discovers the local diagonal-module dependency automatically. Independent replay compiled the canonical source at `f606af160664c5a10952e9a957b100a1cd45bbeb` and the notebook sources with Lean 4.33.1, then checked the resulting modules using `leanchecker`. The three public theorems print only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the derivation and formalization. [Notebook replay](../../README.md)
