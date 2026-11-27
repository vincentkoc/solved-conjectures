# Green 33 · energy above a representation cutoff

Let `r(s)` count ordered pairs from a cyclic two-basis `A` that sum to `s`. Write `k = |A|` and let `q` be the group order. If `q → ∞` and `k/√q → √2`, then for every fixed natural cutoff `M` and every real `c < 2`, eventually

```text
∑_{s : r(s) > M} r(s)² > c q.
```

The [previous bound](DIVERGENCE.md) forces the largest ordered count to diverge. This theorem quantifies how much energy remains after discarding **all** residues at or below the cutoff. The same conclusion holds for varying cutoffs when `M(k² + k − 2q)/q → 0`. The Lean declarations are `Green33TailEnergy.eventually_lt_tail_energy` and `Green33TailEnergy.eventually_lt_tail_energy_of_cost`. [Proof](Green33TailEnergy.lean)

**Finite estimate.** For every two-basis in a finite abelian group, let `Δ = k² + k − 2q`, twice the number of unordered pairs left over after allocating one to each group element. Then

```text
∑_{s : r(s) > M} r(s)² ≥ (k − 2)² − MΔ − k.
```

To see the leading term, write `d(s)` for the ordered difference count. Equal-sum and equal-difference quadruples correspond by exchanging two entries, so the two counts have equal second moments about any fixed center. Center at 2. The zero-difference fiber alone contributes `(k − 2)²`. For the cutoff estimate, let `b(s)` be the number of diagonal pairs summing to `s`. The local excess `e(s) = r(s) + b(s) − 2` is nonnegative by coverage and sums to `Δ`. For `2 ≤ r(s) ≤ M`, the centered square is at most `M e(s)`. A singleton fiber costs one unit and is diagonal, so the total singleton cost is at most `∑ b(s) = k`. Above the cutoff, the full square covers the centered square. Dividing by `q` gives the claimed asymptotic bound. Li and Chen use the same sum/difference energy principle in Lemma 2.1. [Li and Chen, *On additive representation functions*](https://doi.org/10.1017/S0004972717000302)

**Upstream scope.** The limit uses precisely the positive cyclic moduli, sumset coverage, and size normalization of `Green33.green_33`. The upstream conjecture asks whether arbitrarily large moduli admit such bases at each positive tolerance. Here the asymptotically optimal family is a hypothesis. Its existence remains open. [Pinned declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Green, problem 33](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.33)

**Tracker check.** DeepMind’s issue and merged PR concern the statement. The LTS target listed no solution, live agents, or reduction steps. Searches of the LTS solved feed and open and closed OMA issues and PRs found no matching proof. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [LTS target](https://lefttosolve.com/api/problems/Green33.green_33) · [LTS solved feed](https://lefttosolve.com/api/solved) · [OMA search](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%22Green33%22)

**Replay.** Set `FC` to the Formal Conjectures checkout with the pinned dependencies and Lean 4.33.1. Run from the notebook root in Bash. The theorems print only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with this formalization.

```bash
set -e
src="$PWD/research/green"
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
cd "${FC:?set FC to the Formal Conjectures checkout}"
lake env bash -eu -c '
  cd "$2"
  export LEAN_PATH="$1:$LEAN_PATH"
  for module in Green33Multiplicity Green33TailEnergy; do
    lean -o "$1/$module.olean" "$module.lean"
  done
  leanchecker -v Green33Multiplicity Green33TailEnergy
' replay "$out" "$src"
```
