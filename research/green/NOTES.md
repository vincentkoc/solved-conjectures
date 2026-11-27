# Green 33 · bounded representation multiplicity

**Partial result.** Write `q ≥ 1`, `k = |A|`, and let `r(s)` count **ordered** pairs in `A × A` with sum `s`. For every cyclic two-basis `A + A = ℤ/qℤ` and every natural `m`, Lean proves

```text
(∀ s, r(s) ≤ m + 4)  ⇒  (2m + 2)q + 6 ≤ m k² + (m + 8)k.
```

For fixed `m > 0`, divide by `q`. Along a family with `q → ∞` and `k/√q → c`, the linear term vanishes, so `c² ≥ 2 + 2/m`. Thus any family attaining Green’s constant `√2` must have `max r(s) → ∞`. This limit statement is an algebraic consequence of the checked finite inequality. Existence of such a family remains open.

**Upstream.** At `f606af160664c5a10952e9a957b100a1cd45bbeb`, `FormalConjectures/GreensOpenProblems/33.lean`, declaration `Green33.green_33` asks for every real `ε > 0` for infinitely many positive moduli `q` admitting a basis with `|k/√q − √2| < ε`. The proof here assumes only sumset coverage and the displayed pointwise cap and works for every positive modulus, including composite ones. [Pinned statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Green, problem 33](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.33)

**Counting argument.** Interchanging two entries in a quadruple equates the sum and difference energies. The zero-difference fiber has size `k`. Every other fiber of integer size `d` satisfies `d² ≥ 5d − 6`. On the sum side, an ordered singleton representation must be a double. There are at most `k` such residues. On the other fibers expand `(r − 2)(m + 4 − r) ≥ 0` and sum. The energy method has prior literature, including Li–Chen, Lemma 2.1. Their Theorem 1.1 also gives a qualitative obstruction to bounded multiplicity at Green’s density. [Li–Chen (2017)](https://doi.org/10.1017/S0004972717000302)

**Duplicate check.** Searched open and closed DeepMind and OMA issues and PRs by declaration, namespace, path, problem number/title and thin additive bases. DeepMind’s issue and merged PR add the statement. No matching proof or in-flight PR surfaced. The LTS target had no solution, live agents or reduction steps, and the complete solved feed had no `Green33.*` entry. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [OMA search](https://github.com/GuillaumeBAUD-coder/open-math-agents/pulls?q=is%3Apr+%22green_33%22) · [LTS target](https://lefttosolve.com/api/problems/Green33.green_33) · [LTS solved feed](https://lefttosolve.com/api/solved)

**Replay** from the research worktree root. The file prints the axioms of `Green33Multiplicity.multiplicity_bound`: `propext`, `Classical.choice`, `Quot.sound`.

```sh
proof="$PWD/research/green/Green33Multiplicity.lean"
(source ~/formal-math/env.sh && cd ~/formal-math/fc && lake env lean "$proof")
```
