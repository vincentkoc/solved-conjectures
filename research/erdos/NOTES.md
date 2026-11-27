# Erdős 722 — binary Steiner quadruple systems

**Partial coverage.** The pinned declaration `Erdos722.erdos_722` asks for every `1 ≤ r < k` and all sufficiently large `n` satisfying the binomial divisibility conditions. Keevash proved that theorem. The file here proves the family `r = 3`, `k = 4`, `n = 2^d` directly. Other admissible orders and other parameters remain outside this proof. [Pinned source at `f606af160664c5a10952e9a957b100a1cd45bbeb`](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/722.lean) · [Problem 722](https://www.erdosproblems.com/722) · [Keevash, Theorem 1.4](https://arxiv.org/pdf/1401.3665)

`Erdos722.exists_binary_quadruple_design` gives `∃ H : Finset (Finset (Fin (2 ^ d))), H.IsBlockDesign 3 4` for every natural `d`. For `d ≥ 2` the design has blocks. For `d = 0, 1` there are no triples. Label the points by binary vectors and take all zero-sum four-sets. A triple has a unique completion given by its vector sum. If that sum were already in the triple, the other two vectors would be equal. [Binary Hamming codes and Boolean designs, Remarks 2.1(ii)](https://link.springer.com/article/10.1007/s10623-021-00853-z)

**Duplicate check, 2026-11-28.** DeepMind issues and PRs, open and closed, were searched by problem number/title, declaration, path, and construction. The original PR added the statement. A related PR concerns asymptotic packings and coverings. LTS listed `Erdos722.erdos_722` as unsolved with zero active agents and no 722 entry in its solved ledger. OMA PR searches (including merged PRs) and its local proofs/reductions found no matching formalization. [Original statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5495) · [Packing/covering PR](https://github.com/google-deepmind/formal-conjectures/pull/4248) · [LTS target](https://lefttosolve.com/api/problems?q=Erdos722) · [LTS solved](https://lefttosolve.com/solved) · [OMA search](https://github.com/GuillaumeBAUD-coder/open-math-agents/pulls?q=is%3Apr+Erdos722)

**Replay from the research worktree.** The file imports the upstream block-design predicate directly. Its final axiom check reports `[propext, Classical.choice, Quot.sound]`.

```sh
proof="$(pwd)/research/erdos/Erdos722BinaryQuadruples.lean"
source ~/formal-math/env.sh
(cd ~/formal-math/fc && lake env lean "$proof")
```
