# A two-sided Fourier bound for the theta sum

At every odd prime `p`, with `m = (p−1)/2` and `H_m = 1 + 1/2 + ⋯ + 1/m`, the canonical sum satisfies

```text
|p S(p) + 2m²| ≤ 4p² H_m².
```

In particular, `|S(p)| ≤ p [1 + 4(1 + log p)²]`. The Lean theorem `S_isBigO_prime_log_sq` also states `S(p) = O(p log² p)` on the filter of primes tending to infinity. For every `ε > 0`, the sum is therefore `o(p^(1+ε))` along the primes. In particular, for every `C > 0` and `ε > 0`, all sufficiently large primes satisfy `S(p) < C p^(1+ε)`. This proves the upper inequality of the paper’s revised Conjecture 3.3. Its lower inequality requires `C₁p < S(p)` for every positive `C₁`; the pinned DeepMind declaration `conjecture_4_4` formulates this lower growth condition using natural multipliers. Positivity and the lower inequality remain open. [Conjecture 3.3, v3, p. 4](https://arxiv.org/pdf/2501.03234v3#page=4) [Proof](ThetaFourierBound.lean) · [Pinned upstream declarations](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean#L41-L95)

The [composite-denominator estimate](COMPOSITE-DENOMINATORS.md) identifies the gcd correction at odd moduli and gives an explicit negative leading term on powers with at least three distinct prime factors.

## Proof

Let `A = {1, 3, …, p−2}` in the field of residues modulo `p`, and count ordered pairs `N = #{(a,b) ∈ A² : ab ∈ A}`. The [odd-representative identity](DIAGONAL.md) gives `S(p) = 4N − 2m²`. With `e(x) = exp(2πix/p)`, put `F(t) = Σ_{a∈A} e(at)` and `L = Σ_{t≠0} |F(t)|`.

Fourier inversion gives `pN = Σ_t F(−t) Σ_{a∈A} F(at)`. The term at zero is `m³`. For each nonzero `t`, the residues `at` with `a ∈ A` are distinct and nonzero, so the inner sum has magnitude at most `L`. Thus `|pN − m³| ≤ L²`.

Since `A` is an arithmetic progression of step two, the geometric-series formula bounds `|F(t)|` by `2/|e(2t)−1|` at nonzero frequencies. Doubling permutes these frequencies. Pair `n` with `p−n` and use `sin(πn/p) ≥ 2n/p` for `1 ≤ n ≤ m` to obtain `L ≤ pH_m`. Substituting `p = 2m+1` gives `pS(p) + 2m² = 4(pN−m³)` and the displayed estimate.

## Comparison with prior work

Berndt et al., Theorem 6.3, give a lower bound with leading term `−p²/4`. The two-sided estimate here has smaller order of magnitude on both sides of zero. The DeepMind issue reduces positivity to a signed row discrepancy. OMA's reductions use finite verification and a lower bound on a harmonic block of rows. Taking absolute values here loses the sign that both approaches need. [Paper, §6](https://arxiv.org/html/2501.03234v3#S6) · [DeepMind row reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA finite reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7053) · [OMA harmonic reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6519)

The order `O(p log² p)` also follows from classical results. Odd-numerator rows vanish. For even `h`, the Hardy–Dedekind identity expresses the row as `4s(h,p) − 8s(h+p,2p)` for the classical Dedekind sum `s`. Summing absolute values is bounded by the complete absolute sums at moduli `p` and `2p`, each of order at most `p log² p` by the known first absolute moment estimate. The notebook supplies a direct finite Fourier proof with an explicit centered inequality. The live DeepMind, OMA and LTS checks on 2026-11-28 found no matching formal result. [Hardy–Dedekind identity, Theorems 3 and 5](https://www.mdpi.com/2297-8747/21/3/31) · [Girstmair and Schoißengeier, equation (1)](https://www.impan.pl/shop/en/publication/transaction/download/product/82121) · [LTS solved records](https://lefttosolve.com/api/solved)

## Replay

From the notebook root, set `FC` to the pinned Formal Conjectures checkout with its Lean 4.33.1 cache. This checks both notebook modules and replays their declarations with the kernel.

```bash
theta="$PWD/research/arxiv/theta-sum"
(cd "${FC:?set FC to the Formal Conjectures checkout}" &&
  lake env python3 - "$theta" <<'PY'
import os, subprocess, sys, tempfile
from pathlib import Path

source = Path(sys.argv[1])
modules = ["ThetaDiagonalModEight", "ThetaFourierBound"]
with tempfile.TemporaryDirectory() as build:
    env = dict(os.environ, LEAN_PATH=build + os.pathsep + os.environ["LEAN_PATH"])
    for mod in modules:
        subprocess.run(["lean", "-R", source, "-o", Path(build) / (mod + ".olean"),
                        source / (mod + ".lean")], env=env, check=True)
    subprocess.run(["leanchecker", "-v", *modules], env=env, check=True)
PY
)
```

The Fourier file prints the axioms for all five public theorems. Each uses only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the derivation and formalization.
