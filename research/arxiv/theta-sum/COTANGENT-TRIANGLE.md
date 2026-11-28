# A positive logarithmic contribution to the prime theta sum

For every odd prime `p`, the canonical theta sum admits a decomposition `S(p) = U(p) + R(p)` with

```text
U(p) ≥ 3p H_⌊p/6⌋ / (4π²) ≥ [3/(4π²)] p log(p/6).
```

Here `H_n` is the harmonic number. In particular, the upper triangle alone exceeds any fixed multiple of `p` for all sufficiently large primes. The remaining term `R(p)` is an explicit weighted sum of parity signs at odd moduli strictly smaller than `p`. [Lean proof](ThetaCotangentTriangle.lean) · [Pinned definitions and conjectures](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean#L36-L95)

Write `w(u) = cot(πu/(2p))` for odd `1 ≤ u < p`, and let `s_m(a)` be +1 when the least nonnegative representative modulo `m` is odd and −1 otherwise. Bars below denote modular inverses in the indicated modulus. Both sums run over odd positive indices.

```text
U(p) = (2/p) Σ_{u ≤ v < p} w(u) w(v) s_p(v ū)
R(p) = (2/p) Σ_{v < u < p} w(u) w(v) s_u(v p̄)
```

The second triangle can have either sign. Direct evaluation of the original floor sum gives `S(41) = 80`, with `U ≈ 86.4791` and `R ≈ −6.4791`. At 73 the values are `200`, `170.2121` and `29.7879`. Both primes are 1 modulo 8.

## Proof

Extend the parity sign to the prime field by setting its value at zero to zero. Its unnormalized additive Fourier coefficient at frequency `t` is `(z−1)/(z+1)` for `z = exp(2πit/p)`, by a geometric series. At `t = (p−u)/2` the coefficient is `i w(u)`. Orthogonality applied to the parity correlation `Σₓ s_p(x)s_p(ax)` and the odd-representative formula for the original sum give the double cotangent sum with sign `s_p(v ū)`. [Earlier row identity](RATIONAL-ROWS.md) · [Formal cotangent identity](ThetaCotangentTriangle.lean)

Choose the unique `k ∈ {0,…,u−1}` for which `u` divides `v+kp`. Then `(v+kp)/u` is the least representative of `v ū` modulo `p`, and its parity sign is `(−1)^k`. As `v` advances through odd numerators in steps of two, the carries traverse all residues modulo `u` once per full block. The signs sum to one on a full block. Every prefix has sum at least `−⌊u/2⌋`. For `v < u`, the carry is the negative of the nonzero residue `v p̄` modulo `u`, giving the sign in `R(p)`.

Summation by parts with the decreasing weights gives `Σ_{v ≥ u} w(v) s_p(v ū) ≥ −⌊u/2⌋ w(u) ≥ −p/π`. For `u = 1` all signs are positive. Write `M = Σᵥ w(v)`. Since `w(1) ≥ 3p/(2π)`, the first row absorbs every allowable deficit and leaves `U(p) ≥ M/π`. Finally `w(u) ≥ 3p/(2πu)` when `3u ≤ p`. Summing this estimate gives the stated harmonic bound.

## Remaining sign estimate

If some real `b < 3/(4π²)` satisfies `R(p) ≥ −b p log p` eventually along odd primes, then for every natural `n` one has `n p < S(p)` eventually along those primes. The theorem `growth_of_lowerTriangle` checks these quantifiers against pinned Conjecture 4.4. The notebook proves the triangle estimate unconditionally. The displayed hypothesis on `R`, the paper's lower growth inequality and positivity at all odd primes remain open. [Paper, revised Conjecture 3.3](https://arxiv.org/pdf/2501.03234v3#page=4) · [Earlier two-sided upper bound](FOURIER.md)

Sczech's equation (8) gives a cotangent formula for the individual theta transformation sum. Lägeler discusses its relation to Hardy sums. The present proof uses finite Fourier orthogonality and an incomplete-period estimate for the full triangular contribution. The live DeepMind and OMA issues and pull requests and the LTS solved records checked on 2026-11-28 contained the row-discrepancy, finite and short-row harmonic reductions. The search found no matching triangular estimate. [Sczech, pp. 234–235](https://doi.org/10.2206/kyushujm.49.233) · [Lägeler, introduction](https://doi.org/10.1007/s12188-024-00283-3) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6519) · [LTS solved records](https://lefttosolve.com/api/solved)

The clean replay compiled the canonical source at `f606af160664c5a10952e9a957b100a1cd45bbeb`, both local dependencies and the triangle module using Lean 4.33.1. Independent kernel replay covered all three local modules. The nine public triangle theorems and the three shared parity and reindexing lemmas print only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the derivation and formalization. [Notebook replay](../../README.md)
