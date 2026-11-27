# A half-factorial formula modulo eight

Let `p` be an odd prime, `m = (p−1)/2`, and `χ` the Legendre symbol modulo `p`. For the canonical theta sum,

```text
S(p) ≡ 2(m−1)² − 2χ(2^m m!)    (mod 8).
```

For `p ≡ 3 (mod 4)`, this simplifies to **`S(p) ≡ −2χ(2m!) (mod 8)`**. A square value of `2m!` gives residue 6, and a nonsquare gives residue 2. For example, the predicted residues at 7 and 11 are 2 and 6, respectively. Together with the [one-mod-four theorem](DIAGONAL.md), this determines the residue at every odd prime. Positivity and nonvanishing at primes congruent to 1 modulo 8 remain open. [Lean proof](ThetaGaussFactorial.lean) · [Canonical definitions and hypotheses](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean#L41-L95)

## Proof

The previous diagonal formula gives `S(p) ≡ 2[m(m−1)+D] (mod 8)`. Here `D` counts odd square representatives with sign +1 and even ones with sign −1, using exactly one root from each pair `{a,−a}`. Each nonzero square has exactly one root with odd least representative. Thus `D = m−2E`, where `E` is the number of even quadratic residues among `2,4,…,2m`.

Exactly `E` of the `m` signs `χ(2k)` are positive, so `D = −Σ χ(2k)`. For any `m` signs, their sum is congruent modulo four to `m−1` plus their product. Multiplicativity makes that product `χ(2^m m!)`. Substitution gives the first formula. When `m` is odd, `2(m−1)²` vanishes modulo eight and `χ(2)^m = χ(2)`, giving the half-factorial form.

## Scope and replay

The proof imports the earlier diagonal theorem and uses Mathlib's `legendreSym` on the stated integers. It sharpens the pointwise residue in Proposition 7.1. The quadratic character distinguishes two residues of the integer sum and leaves its sign undetermined. Live DeepMind and OMA issues and PRs and the LTS solved feed yielded no matching factorial reduction on 2026-11-28. [Paper, §7](https://arxiv.org/html/2501.03234v3#S7) · [DeepMind row reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA multiplicative-parity reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7053) · [LTS solved records](https://lefttosolve.com/api/solved)

From the notebook root, set `FC` to the pinned Formal Conjectures checkout with its Lean 4.33.1 cache.

```bash
theta="$PWD/research/arxiv/theta-sum"
(cd "${FC:?set FC to the Formal Conjectures checkout}" &&
  lake env python3 - "$theta" <<'PY'
import os, subprocess, sys, tempfile
from pathlib import Path

source = Path(sys.argv[1])
modules = ["ThetaDiagonalModEight", "ThetaGaussFactorial"]
with tempfile.TemporaryDirectory() as build:
    env = dict(os.environ, LEAN_PATH=build + os.pathsep + os.environ["LEAN_PATH"])
    for mod in modules:
        subprocess.run(["lean", "-R", source, "-o", Path(build) / (mod + ".olean"),
                        source / (mod + ".lean")], env=env, check=True)
    subprocess.run(["leanchecker", "-v", *modules], env=env, check=True)
PY
)
```

All three public theorems print only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the derivation and formalization.
