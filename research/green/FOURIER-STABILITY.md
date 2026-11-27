# Green 33 · Fourier stability of thin two-bases

Let `A + A = G` in a finite abelian group of order `q`, with `k = |A|`. For a nontrivial complex additive character `χ`, write `Sχ = ∑_{a∈A} χ(a)`. The finite estimates are

```text
|Sχ² + ∑_{a∈A} χ(2a)| ≤ k(k + 1) − 2q,
                  |Sχ|² ≤ k² + 2k − 2q.
```

In the cyclic groups of Green 33, suppose `q → ∞` and `k/√q → √2`. Then `|Sχ|/√q → 0`, even when the nontrivial character is chosen separately for each modulus. Thus a family attaining Green's density must have small normalized character sums at every nonzero frequency. [Checked finite and limiting theorems](Green33FourierStability.lean)

**Why the diagonal appears.** Let `r(s)` count ordered pairs summing to `s` and `d(s)` count their diagonal pairs. Then `r(s) + d(s)` counts unordered representations twice. Coverage gives `e(s) = r(s) + d(s) − 2 ≥ 0`, and summing gives `∑ e(s) = k(k + 1) − 2q`. Weight by `χ(s)` and sum again. Orthogonality kills the constant term, the ordered pairs contribute `Sχ²`, and the diagonal contributes `∑ χ(2a)`. The triangle inequality bounds the modulus by `∑ e(s)`. Removing the diagonal correction costs at most `k`. Dividing the second bound by `q` gives the limiting conclusion.

**Scope.** The finite bounds require only coverage and a nontrivial character. The limit specializes to the upstream positive moduli, coverage equality and size normalization. It assumes a family attaining the proposed density. The existence of that family remains open. This is a formalization of a counting and character-orthogonality argument. Li and Chen study related representation bounds by energy methods. [Green 33](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.33) · [Pinned Lean declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Li and Chen](https://doi.org/10.1017/S0004972717000302)

**Tracker check.** The DeepMind issue and merged PR cover the problem statement. The LTS target and solved feed, and the open and closed OMA issues and PRs, showed no matching formalization. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [LTS target](https://lefttosolve.com/api/problems/Green33.green_33) · [LTS solved feed](https://lefttosolve.com/api/solved) · [OMA search](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%22Green33%22)

**Replay.** From the notebook root, set `FC` to the Formal Conjectures checkout with its pinned Mathlib and Lean 4.33.1. Run in Bash. The three public theorems print only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the formalization.

```bash
set -e
src="$PWD/research/green"
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
cd "${FC:?set FC to the Formal Conjectures checkout}"
lake env bash -eu -c '
  export LEAN_PATH="$1:$LEAN_PATH"
  cd "$2"
  lean -o "$1/Green33FourierStability.olean" Green33FourierStability.lean
  leanchecker -v Green33FourierStability
' replay "$out" "$src"
```
