# A diagonal congruence modulo eight

For every prime `p` congruent to 1 modulo 4, **`S p ≡ p − 1 (mod 8)`**. In particular, at primes congruent to 5 modulo 8, the sum is 4 modulo 8 and has absolute value at least four. Together with the [modulo-four theorem](NOTES.md), this confines a possible zero at an odd prime to the class 1 modulo 8. The sign in all four odd classes remains open in general. [Lean proof](ThetaDiagonalModEight.lean)

## Why the diagonal matters

Let `O` be the units modulo `p` whose least positive representative is odd. Put `m = (p−1)/2` and let `ε(x)` be +1 for an odd representative and −1 for an even one. Negation pairs odd and even representatives. In the original double sum, this cancels every even column and turns each odd column into twice its sum over odd rows. Thus

```text
S(p) = 2 Σ_{a,b ∈ O} ε(ab).
```

In the symmetric matrix `ε(ab)`, each off-diagonal pair contributes 2 modulo 4. This gives a formula at **every odd prime**.

```text
S(p) ≡ 2 [m(m−1) + Σ_{a ∈ O} ε(a²)]  (mod 8).
```

When `p ≡ 1 (mod 4)`, choose a square root `i` of −1. Multiplication by `i` permutes all units and reverses the sign of the square, since `ε(−x) = −ε(x)`. The sum over all units is therefore zero. Squaring identifies the terms at `a` and `−a`, so the sum over `O` is zero as well. Substituting `m = 2t` gives `2m(m−1) ≡ 4t = p−1 (mod 8)`.

## Scope and prior work

The proof imports the original `Arxiv.«2501.03234».S`, including its rational floor and both half-open summation intervals. The main theorem assumes only primality and `p % 4 = 1`, which implies the oddness required by DeepMind. Its nonvanishing corollary leaves open the strict inequality in `conjecture_1_1` and every growth conjecture. The source paper gives the pointwise modulo-four result in Proposition 7.1. [Canonical Lean declarations](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean) · [Berndt et al., §7](https://arxiv.org/html/2501.03234v3#S7)

The DeepMind issue uses row reflection and interval discrepancy. OMA's finite reduction also uses multiplicative parity correlations. Here the additional step is to isolate the diagonal modulo eight and cancel its sum when −1 is a square. The search of open and closed DeepMind and OMA records and the LTS solved feed on 2026-11-28 found no matching formal theorem. This is a notebook result, with no priority claim. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA finite reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7053) · [OMA long-row reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6519) · [LTS solved feed](https://lefttosolve.com/api/solved)

## Replay

From the notebook root, with `FC` pointing to the pinned Formal Conjectures checkout:

```sh
proof="$PWD/research/arxiv/theta-sum/ThetaDiagonalModEight.lean"
(cd "$FC" && lake env lean "$proof")
```

The file audits all five public theorems. Each uses only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the derivation and formalization.
