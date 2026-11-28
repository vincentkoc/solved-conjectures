# How often do primes start Cunningham chains?

Fix a positive length `k` and either recurrence `p ↦ 2p ± 1`. Among seeds up to `x`, the number whose first `k` terms are prime is **Oₖ(x/(log x)ᵏ)**. The same unconditional bound holds with Jones’s additional requirement that the next term be composite. This is a specialization of the classical upper-bound sieve for simultaneous prime values of polynomials. Bordignon and Simpson Lee give explicit bounds for general polynomial families, including a worked Sophie Germain example. [Lean proof](CunninghamSelbergSieve.lean) · [Bordignon and Simpson Lee](https://arxiv.org/abs/2211.11012) · [Elkies’s quadratic sieve notes](https://people.math.harvard.edu/~elkies/M229.15/sieve.pdf)

Let `Pₖ(x)` count prime prefixes and `Eₖ(x)` count exact chains for the selected sign. The pinned definitions give `Pₖ − Eₖ = Pₖ₊₁` identically. Thus the stopping error is **Oₖ(x/(log x)ᵏ⁺¹)**. For any fixed `C > 0`, the asymptotic `Pₖ(x) ∼ Cx/(log x)ᵏ` is equivalent to the same asymptotic for `Eₖ(x)`. The earlier application of Bateman–Horn used leading asymptotics at two successive lengths. The new equivalence needs only the proposed asymptotic at the length of interest. For `k ≥ 2`, a matching lower bound and Jones’s infinitude conjecture remain open. [Canonical predicates](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean) · [Conditional counts](BatemanHornCounts.md) · [Jones](https://arxiv.org/abs/1104.1579)

At length one, `P₁(x) = π(⌊x⌋)`. The bound for `P₂` and Chebyshev’s lower bound for the primes give **E₁(x) ∼ π(⌊x⌋)** for each sign. The proportion of primes whose successor is composite therefore tends to one. [Lean proof](CunninghamSelbergSieve.lean) · [Earlier reciprocal-sum result](BrunReciprocals.md)

For a prime `q > 2ᵏ + 2k + 2`, the `k` terms vanish on distinct residues. Assign weight `−1` to those residues and `h(q) = k/(q−k)` to the others. The weight has mean zero and mean square `h(q)`. Products over different squarefree moduli are orthogonal over a full common period by the Chinese remainder theorem. Truncating to moduli at most `y` bounds the total error from incomplete periods by `2y⁴`. A factorial estimate gives `∑ (log q)/q ≤ 2 log z` for primes through `z`. With `y = z^(4k)`, at least half the mass of the associated Euler product lies at moduli at most `y`. A harmonic-sum lower bound supplies the power `(log z)ᵏ`. Choosing `z = ⌊x^(1/(16k))⌋` controls the periodic error and gives the claimed count. [Lean proof](CunninghamSelbergSieve.lean)

The four exported theorems belong to `CunninghamChain`.

| Declaration | Conclusion |
| --- | --- |
| `primePrefixSeedCount_isBigO` | Upper bound for prime prefixes. |
| `exactChainCount_isBigO` | Upper bound for either upstream exact-length predicate. |
| `primePrefixSeedCount_asymptotic_iff_exact` | Equivalence of the leading asymptotics at fixed length and constant. |
| `exactChainCount_one_asymptotic_primeCounting` | Unconditional relative asymptotic among primes at length one. |

Each declaration uses only `propext`, `Classical.choice` and `Quot.sound`. Searches of DeepMind and OMA issues and pull requests and the LTS solved records found no matching formalization. The DeepMind Hardy–Littlewood issue concerns fixed additive offsets. The LTS prime-tuples record concerns an irrationality implication. Codex assisted with the proof. [Cunningham issue](https://github.com/google-deepmind/formal-conjectures/issues/4755) · [Hardy–Littlewood issue](https://github.com/google-deepmind/formal-conjectures/issues/4996) · [LTS prime-tuples record](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2980) · [Notebook replay](../../README.md#replay)
