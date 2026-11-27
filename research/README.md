# DeepMind proof notebook

These Lean files develop partial results for six problems in [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/tree/f606af160664c5a10952e9a957b100a1cd45bbeb). Codex assisted with the proofs. Each file prints its theorem’s axioms. The notes link the original question, prior work and the proof.

| Problem | Kernel-checked result | What remains |
| --- | --- | --- |
| [Green 33](green/NOTES.md) | Every basis satisfies [`2q ≤ k² + 2`](green/REFLECTION-RIGIDITY.md), with exact reflection symmetry at equality. A pointwise cap of `m + 4` implies `(2m + 2)q + 6 ≤ m k² + (m + 8)k`. Along every family with `q → ∞` and `k/√q → √2`, the [maximum ordered count tends to infinity](green/DIVERGENCE.md). All [nontrivial character sums](green/FOURIER-STABILITY.md) are then `o(√q)`. Residues above any fixed cutoff carry [at least `(2 − o(1))q` of the energy](green/TAIL-ENERGY.md). | Existence of a family attaining this density remains open. |
| [Green 33 · order-three quotient](green/ORDER-THREE.md) | If `3 ∣ q`, equality in `2q ≤ k² + 2` forces `4k − 7` to be a square. This raises the size bound by one at every `q = 2(15n + 5)² + 1`, with exact minimum 11 at `q = 51`. | The obstruction concerns exact finite equality. |
| [Cunningham chains](arxiv/NOTES.md) | Dickson’s prime-tuples conjecture implies infinitely many first-kind chains of every positive **exact** length. The proof forces the next term to be composite. | Dickson’s conjecture is an explicit hypothesis. The unconditional first-kind statement remains open. |
| [First-kind chains in residue classes](arxiv/1104.1579/FirstKindProgressions.md) | Under Dickson, a class contains infinitely many exact length-`k` seeds iff each of its first `k` terms is coprime to the modulus. A failed test leaves at most one seed unconditionally. | Infinitude in admissible classes remains conditional. |
| [Second-kind Cunningham chains](arxiv/1104.1579/CunninghamSecondKindDickson.md) | Under Dickson, infinitely many seeds have each positive exact length for the recurrence `p ↦ 2p − 1`. | Unconditional infinitude remains open. |
| [Unbounded Cunningham prefixes](arxiv/1104.1579/UnboundedPrefixes.md) | For each kind, Jones’s full exact-length infinitude statement is equivalent to the existence of one prime prefix of each length. The equivalence is unconditional. | Existence of arbitrarily long prime prefixes remains open. |
| [Erdős 722](erdos/NOTES.md) | The binary construction gives orders `2^d`. [Harmonic quadruples](erdos/HarmonicQuadruples.md) give orders `3^d+1` for every positive `d`, disjoint from the binary orders for `d ≥ 2`. | The general theorem covers all sufficiently large admissible orders for every pair of block and subset sizes. |
| [Erdős 478](erdos/478/NOTES.md) | For primes `p > 5` with 5 a square modulo `p`, at least four factorial residues are missing. [Mixed gaps](erdos/478/MixedGaps.md) give five missing residues for arbitrarily large such primes. Along a strictly increasing sequence in this class, the [number missing tends to infinity](erdos/478/UnboundedDeficit.md). | The conjecture asks for a limiting proportion along all primes. |
| [Theta sum](arxiv/theta-sum/NOTES.md) | The [half-factorial formula](arxiv/theta-sum/GAUSS-FACTORIAL.md) determines `S(p) mod 8` for odd primes. A zero requires `p ≡ 1 (mod 8)` and [odd-nonresidue product `+1`](arxiv/theta-sum/MOD-SIXTEEN.md). The [Fourier bound](arxiv/theta-sum/FOURIER.md) proves the upper inequality in v3 Conjecture 3.3. | Positivity and the lower growth inequality remain open. |
| [Lucas–Fibonacci sums](arxiv/2211.10788/NOTES.md) | In every positive-step arithmetic progression of indices, the composite terms have infinitely many distinct prime divisors between them. | The upstream question asks whether infinitely many terms are themselves prime. |
| [Lucas–Fibonacci excluded primes](arxiv/2211.10788/ExcludedPrimeDivisors.md) | Every prime congruent to 13, 17, 21, 29 or 41 modulo 44 divides no term. Each class contains infinitely many primes. | Infinitude of prime values remains open. |
| [Neighboring Lucas–Fibonacci prime pairs](arxiv/2211.10788/NeighboringPrimePairs.md) | After index 6, both neighbors are prime iff the index is 0, 6 or 18 modulo 24 and `11Fₙ² − 1` is semiprime. | Existence of another pair remains open. |

## Replay

Use Python 3.9 or newer and a Formal Conjectures checkout at `f606af160664c5a10952e9a957b100a1cd45bbeb` with its pinned Lean 4.33.1 dependencies. From this repository’s root, set `FC` to the path of that checkout and run:

```bash
runner="$PWD/scripts/replay-research"
(cd "${FC:?set FC to the Formal Conjectures checkout}" && lake env python3 "$runner")
```

The runner discovers every `.lean` file under `research/`, resolves its imports with Lean, and compiles notebook dependencies first. Use a unique module filename for each proof. Each file must print its theorem’s axioms. The runner checks the reports against `propext`, `Classical.choice` and `Quot.sound`, then replays all compiled notebook modules with `leanchecker`. Compiled notebook files are temporary.

The [theta Fourier replay](arxiv/theta-sum/FOURIER.md#replay) first compiles its diagonal-module dependency.
