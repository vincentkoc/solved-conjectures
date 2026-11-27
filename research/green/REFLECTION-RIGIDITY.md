# Green 33 · group order and reflection symmetry

Every two-basis `A + A = G` of size `k` in a finite abelian group of order `q` satisfies

```text
2q ≤ k² + 2.
```

The additive constant is sharp. In the cyclic group of order 9, the four elements `{0, 1, 3, 4}` cover every residue by sums. Both the bound and this example are checked in Lean. [Proof](Green33ReflectionRigidity.lean)

**Reflection.** There is a sum `s` such that at most `max(k² − 2q, 0) + 1` elements of `A` lack a partner `s − a` in `A`. Deleting precisely those elements leaves a set invariant under the reflection. In particular, if `k² ≤ 2q`, at most one deletion suffices. At equality in the order bound, `2q = k² + 2`, the whole basis is invariant. No diagonal pair sums to the center, and every other group element has exactly one **unordered** representation. These statements are `Green33ReflectionRigidity.exists_reflection`, `exists_reflection_of_sq_le` and `extremal_profile`. [Lean declarations](Green33ReflectionRigidity.lean)

**Proof.** Write `r(t)` for the ordered sum count. For any cap `R ≥ max r(t)`, the proof gives

```text
(k − 1)(k − 2) ≤ (R − 1)(k² + k − 2q).
```

The polynomial `P(x) = (x − 1)(x − 2)` is nonnegative on integers. The sum of `P` over the sum counts equals its sum over the difference counts, by their equal second moments about 3/2. The zero difference gives `P(k)`. For the upper bound, let `b(t)` count diagonal pairs. Coverage gives `r + b ≥ 2` and `P(r) ≤ (R − 1)(r + b − 2)`. Summing proves the cap inequality. Taking `R = k` yields the order bound, while taking `R = max r(t)` gives a reflection that preserves exactly `R` elements. When equality forces `R = k`, the center uses the full unordered-pair surplus. The remaining residues therefore have one unordered representation each. [Centered energy identity](Green33TailEnergy.lean)

**Scope and prior work.** Green asks for infinitely many cyclic moduli with bases of size approaching `√(2q)` to relative error tending to zero. The finite bound gives `k ≥ √(2q − 2)`. Existence at the proposed asymptotic density remains open. The one-deletion conclusion uses the stronger finite condition `k² ≤ 2q`. Haanpää treats finite abelian sum covers and the unordered-pair counting bound. Li and Chen compare ordered sum and difference energies. [Pinned Green 33 declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Haanpää, §2](https://cs.uwaterloo.ca/journals/JIS/VOL7/Haanpaa/haanpaa.pdf) · [Li and Chen, Lemma 2.1](https://doi.org/10.1017/S0004972717000302)

**Tracker check.** The DeepMind issue and merged PR concern the statement. The LTS target listed no solution or steps, and the solved feed had no Green 33 entry. Open and closed OMA issues and PRs showed no matching formalization. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [LTS target](https://lefttosolve.com/api/problems/Green33.green_33) · [LTS solved feed](https://lefttosolve.com/api/solved) · [OMA search](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%22Green33%22)

**Replay.** Set `FC` to the Formal Conjectures checkout with the pinned dependencies and Lean 4.33.1. Run from the notebook root in Bash. Each public theorem prints only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the formalization.

```bash
set -e
src="$PWD/research/green"
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
cd "${FC:?set FC to the Formal Conjectures checkout}"
lake env bash -eu -c '
  cd "$2"
  export LEAN_PATH="$1:$LEAN_PATH"
  for module in Green33Multiplicity Green33TailEnergy Green33ReflectionRigidity; do
    lean -o "$1/$module.olean" "$module.lean"
  done
  leanchecker -v Green33Multiplicity Green33TailEnergy Green33ReflectionRigidity
' replay "$out" "$src"
```
