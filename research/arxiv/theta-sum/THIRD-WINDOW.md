# A signed window of Hardy rows about one third

Let `W(p,L)` be the sum of the paper's original rows `S′(h,p)` over **all even** `1 ≤ h < p` with `|3h−p| < 6L`. For a prime `p` and a positive integer `L` with `300L² ≤ p`, the two prime classes give opposite signs.

| Prime class | Signed contribution |
| --- | --- |
| `p ≡ 1 (mod 3)` | `W(p,L) ≥ p/5` |
| `p ≡ 2 (mod 3)` | `W(p,L) ≤ −p/5` |

For example, direct evaluation of the canonical floor sum gives `W(10007,5) = −2940` and `W(10009,5) = 2964`. This sign law concerns a contiguous window. Positivity of the full sum remains open. [Lean proof](ThetaThirdWindow.lean) · [Pinned definition of the rows and Conjecture 1.1](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean#L36-L64)

## Size of the window sum

Set `s = 1` for primes one modulo three and `s = −1` for primes two modulo three. For every integer `L ≥ 0` with `6L+3 < p`, the effective estimate is

```text
|s W(p,L) − πp/(6√3)| ≤ 18L² + 2L + p/[3(6L+1)].
```

Taking `L` of order `p^(1/3)` gives an error of order `p^(2/3)`. Writing `H_L` for the harmonic number, the subtotal from `3h < p` and the negative of the subtotal from `3h > p` each exceed or equal `p H_L/18 − 9L² − 7L`. Consequently, for every positive `C`, a single fixed width gives opposite signed subtotals of magnitude greater than `Cp` at **every** sufficiently large prime. This extends the earlier negative-mass obstruction beyond its prime progression. [Long rows on prime progressions](RATIONAL-ROWS.md)

## Derivation

Use the odd reflected index `a = p−h`. The row equals `R(a) = Σ_b s₀(b)s₀(ab)`, where `s₀(b)` is +1 for odd least representatives and −1 for even ones. For a reduced odd fraction `u/v` of units modulo `p`, rotating the variable gives a product of two parity waves on the same grid. Their sum on a complete grid of `M = uv` points is one by the Chinese remainder theorem. On the `p`-point grid, bin `t` holds `⌈(t+1)p/M⌉ − ⌈tp/M⌉` points, within one of `p/M`. Summing the bin discrepancies and removing the zero sample gives `|R(u/v) − p/(uv)| ≤ uv+1`.

There are exactly `2L` reflected odd indices in the window. For `0 ≤ k < L`, the offsets `3a−2p` run through `6k+1` and `−(6k+5)` when `p ≡ 1 (mod 3)`, and through their negatives when `p ≡ 2 (mod 3)`. A negative offset negates the corresponding row. The signed main term is therefore `s(p/3) B_L`, where

```text
B_L = Σ_{0 ≤ k < L} [1/(6k+1) − 1/(6k+5)].
```

The row errors sum to at most `18L²+2L`. For `L ≥ 1`, the first pair gives `B_L ≥ 4/5`. Integrating the finite geometric series gives a sharper value. The integral of `(1+x²)/(1+x²+x⁴)` from zero to one is `π/(2√3)`, by two elementary arctangents. The remaining integral has an extra factor `x^(6L)`, so it lies between zero and `1/(6L+1)`. This proves the displayed bound.

## Prior work and verification

Liu and Zhang's Lemma 5 already estimates an individual Hardy row near an odd reduced fraction. At `h/p` near `1/3`, their main term is `−p/[3(3h−p)]` with error `O(|3h−p|+1)`. Summing that classical estimate already gives the leading coefficient on growing windows of width `o(√p)`. The present elementary proof supplies explicit constants, the square-root range for the sign, and kernel-checked inequalities for both contiguous sides. The existing DeepMind discrepancy reduction and OMA short harmonic block treat different row sets. Searches of their issues and PRs and the LTS solved feed on 2026-11-28 found no matching formal window result. [Liu and Zhang, Osaka Journal of Mathematics 41 (2004), Lemma 5](https://doi.org/10.18910/10379) · [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA harmonic block](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6519) · [LTS solved feed](https://lefttosolve.com/api/solved)

The theorem `windowSum_eq_even_interval` identifies the reflected definition with the interval in the pinned source indexing. Independent replay compiled that source from commit `f606af160664c5a10952e9a957b100a1cd45bbeb` and the three notebook modules using Lean 4.33.1, followed by `leanchecker -v`. The public theorem reports list only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the derivation and formalization. [Notebook replay](../../README.md)
