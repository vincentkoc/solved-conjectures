# Green 33 · divergence of the largest sum fiber

For a cyclic two-basis, let `maxReps A` be the maximum over residues of the number of **ordered** pairs in `A × A` with that sum. If the moduli tend to infinity and the basis sizes divided by the square roots of the moduli tend to √2, then the maximum tends to infinity. For every fixed threshold, **every sufficiently late basis** has a residue reaching that threshold. The residue can vary with the basis. [Lean theorem](Green33Divergence.lean)

The hypotheses use the positive moduli, cyclic groups, coverage equality and normalization in `Green33.green_33`. The upstream conjecture asks for arbitrarily large moduli admitting bases within each positive tolerance. Here the theorem takes a family with that limiting density as input. It proves a necessary condition and leaves existence open. The index can be any type with a filter, including a sequence indexed by the natural numbers. [Pinned upstream declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

**Proof.** Write `x = |A|/√q` and fix a natural threshold `m`. If the maximum is below `m`, it satisfies the cap `m + 4` in the finite bound. Dividing that bound by `q` and dropping `6/q` gives

```text
2m + 2 ≤ m x² + (m + 8)x/√q.
```

The right side tends to `2m`, so eventually that inequality is impossible. This formalizes the limiting consequence already described in the notebook. Li and Chen give related energy and representation estimates in finite abelian groups. [Finite proof and prior work](NOTES.md) · [Li and Chen](https://doi.org/10.1017/S0004972717000302)

**Tracker check.** The DeepMind issue and merged PR concern the statement. The Left to Solve target listed no solution, active agents or steps. Searches of its solved feed and of open and closed OMA issues and PRs found no matching formalization. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [LTS target](https://lefttosolve.com/api/problems/Green33.green_33) · [LTS solved feed](https://lefttosolve.com/api/solved) · [OMA search](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%22Green33%22)

**Replay.** From the notebook repository root, set `FC` to a Formal Conjectures checkout with the pinned dependencies and Lean 4.33.1. Run in Bash. Both theorem axiom reports give only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with this formalization.

```bash
set -e
src="$PWD/research/green"
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
cd "${FC:?set FC to the Formal Conjectures checkout}"
lake env bash -eu -c '
  export LEAN_PATH="$1:$LEAN_PATH"
  cd "$2"
  for module in Green33Multiplicity Green33Divergence; do
    lean -o "$1/$module.olean" "$module.lean"
  done
  leanchecker -v Green33Multiplicity Green33Divergence
' replay "$out" "$src"
```
