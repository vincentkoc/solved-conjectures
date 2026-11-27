# First-kind Cunningham chains of exact length

**Partial upstream coverage.** `CunninghamChain.infinitely_many_firstKind_chains_of_primeTuples` proves Jones's implication from Dickson's prime-tuples conjecture. For every natural `k > 0`, infinitely many seeds have their first `k` terms prime and their term at index `k` composite. Dickson is an explicit hypothesis. An unconditional proof for `k = 2` alone would imply infinitely many Sophie Germain primes. [Jones, §1](https://arxiv.org/pdf/1104.1579)

**Pinned comparison.** At `f606af160664c5a10952e9a957b100a1cd45bbeb`, the conclusion is exactly `CunninghamChain.infinitely_many_firstKind_chains` and the hypothesis is the full type of `PrimeTuplesConjecture.prime_tuples_conjecture`, including its `2 ≤ k` restriction on the number of forms. The proof imports both upstream modules. Lean takes the type of the prime-tuples declaration as a hypothesis and uses the original exact-length predicate in the conclusion. [Arxiv/1104.1579/CunninghamChain.lean](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean) · [Paper/PrimeTuples.lean](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Paper/PrimeTuples.lean)

**Proof.** Write `Fᵢ(b)` for term `i` from seed `b`. Apply Dickson once to choose a prime prefix through `q = Fₖ(b)`. Apply it again to the first `k` terms from seeds `q*n + b`. Modulo `q` these terms are the original positive terms strictly below `q`. Modulo any other prime, choose `n` so the seed is `−1`, a fixed point of the recurrence. The next term is `q * (2^k*n + 1)`, composite for every positive `n`.

**Duplicate check, 2026-11-28.** Searches of open and closed DeepMind and OMA PRs/issues by declaration, title, path, arXiv ID and OEIS A181697 found the upstream statement and an OMA reduction splitting length one from the open remainder. Two open OMA PRs cover length one. The LTS solved API had no Cunningham match among 3,124 records. No matching all-length Dickson reduction surfaced. [DeepMind statement](https://github.com/google-deepmind/formal-conjectures/pull/4770) · [OMA reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8693) · [length-one PR](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9857) · [second length-one PR](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9861) · [LTS solved records](https://lefttosolve.com/api/solved)

Replay from the research worktree root. The final axiom report lists only `propext`, `Classical.choice` and `Quot.sound`.

```sh
proof_file="$PWD/research/arxiv/CunninghamChainDickson.lean"
source ~/formal-math/env.sh
(cd ~/formal-math/fc &&
  lake build 'FormalConjectures.Arxiv.«1104.1579».CunninghamChain' FormalConjectures.Paper.PrimeTuples &&
  lake env lean "$proof_file")
```
