# DeepMind proof notebook

These Lean files develop partial results for six problems in [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/tree/f606af160664c5a10952e9a957b100a1cd45bbeb). Codex assisted with the proofs. Each file prints its theorem’s axioms. The notes link the original question, prior work and the proof.

| Problem | Kernel-checked result | What remains |
| --- | --- | --- |
| [Green 33](green/NOTES.md) | A pointwise cap of `m + 4` implies `(2m + 2)q + 6 ≤ m k² + (m + 8)k`. Along every family with `q → ∞` and `k/√q → √2`, the [maximum ordered count tends to infinity](green/DIVERGENCE.md). All [nontrivial character sums](green/FOURIER-STABILITY.md) are then `o(√q)`. Residues above any fixed cutoff carry [at least `(2 − o(1))q` of the energy](green/TAIL-ENERGY.md). | Existence of a family attaining this density remains open. |
| [Cunningham chains](arxiv/NOTES.md) | Dickson’s prime-tuples conjecture implies infinitely many first-kind chains of every positive **exact** length. The proof forces the next term to be composite. | Dickson’s conjecture is an explicit hypothesis. The unconditional first-kind statement remains open. |
| [Second-kind Cunningham chains](arxiv/1104.1579/CunninghamSecondKindDickson.md) | Under Dickson, infinitely many seeds have each positive exact length for the recurrence `p ↦ 2p − 1`. | Unconditional infinitude remains open. |
| [Erdős 722](erdos/NOTES.md) | Every triple of distinct binary vectors extends uniquely to a zero-sum four-set. This gives a Steiner quadruple system on `2^d` points for every `d ≥ 2`. | The general existence theorem is known. This formalization covers the binary construction. |
| [Erdős 478](erdos/478/NOTES.md) | For primes `p > 5` with 5 a square modulo `p`, the factorials from `1!` to `(p−1)!` occupy at most `p−4` residue classes. [Simultaneous quadratic and cubic collisions](erdos/478/MixedGaps.md) improve this to `p−5` for arbitrarily large primes in that class. | The conjecture asks for a limiting proportion along all primes. |
| [Theta sum](arxiv/theta-sum/NOTES.md) | For every odd prime `p`, the sum satisfies `S(p) ≡ p−1 (mod 4)`. The [diagonal congruence](arxiv/theta-sum/DIAGONAL.md) sharpens this to modulo 8 when `p ≡ 1 (mod 4)`. A zero at an odd prime requires `p ≡ 1 (mod 8)`. | Positivity for all odd primes remains open. |
| [Lucas–Fibonacci sums](arxiv/2211.10788/NOTES.md) | In every positive-step arithmetic progression of indices, the composite terms have infinitely many distinct prime divisors between them. | The upstream question asks whether infinitely many terms are themselves prime. |
| [Lucas–Fibonacci excluded primes](arxiv/2211.10788/ExcludedPrimeDivisors.md) | Every prime congruent to 13, 17, 21, 29 or 41 modulo 44 divides no term. Each class contains infinitely many primes. | Infinitude of prime values remains open. |

## Replay

Use Lean 4.33.1 and a Formal Conjectures checkout at `f606af160664c5a10952e9a957b100a1cd45bbeb` with its pinned dependencies. From the root of this notebook’s repository, set `FC` to the path of that checkout and run this in Bash.

```bash
set -e
notebook="$PWD/research"
cd "${FC:?set FC to the Formal Conjectures checkout}"
lake build 'FormalConjectures.Arxiv.«1104.1579».CunninghamChain' FormalConjectures.Paper.PrimeTuples \
  'FormalConjectures.Arxiv.«2501.03234».ArithmeticSumS' \
  'FormalConjectures.Arxiv.«2211.10788».LucasFibonacciSumPrimes'
for proof in \
  "$notebook/green/Green33Multiplicity.lean" \
  "$notebook/green/Green33FourierStability.lean" \
  "$notebook/arxiv/CunninghamChainDickson.lean" \
  "$notebook/arxiv/1104.1579/CunninghamSecondKindDickson.lean" \
  "$notebook/erdos/Erdos722BinaryQuadruples.lean" \
  "$notebook/erdos/478/Erdos478FactorialCollisions.lean" \
  "$notebook/erdos/478/Erdos478MixedGaps.lean" \
  "$notebook/arxiv/theta-sum/ArithmeticSumModFour.lean" \
  "$notebook/arxiv/theta-sum/ThetaDiagonalModEight.lean" \
  "$notebook/arxiv/2211.10788/LucasFibonacciExcludedPrimes.lean" \
  "$notebook/arxiv/2211.10788/LucasFibonacciPrimeDivisors.lean"
do
  lake env lean "$proof"
done
```

Each axiom report lists only `propext`, `Classical.choice` and `Quot.sound`.
