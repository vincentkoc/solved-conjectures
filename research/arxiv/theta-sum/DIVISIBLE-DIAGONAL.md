# The divisible pairs in the theta sum

For every odd prime `p`, the pinned double floor sum has the decomposition

```text
S(p) = (p/2) log p + R(p) + O(p).
```

Here `R(p)` is an explicit sum over odd pairs `1 ≤ u,v < p` with `u ∤ v`. It contains the full off-diagonal contribution from both triangles. The constant in `O(p)` is absolute. Thus a two-sided asymptotic with coefficient one half on a given sequence of primes is equivalent to `R(p) = o(p log p)` on that sequence. The size and sign of this remainder at an individual prime remain open. The previous density-one lower bound concerns the original `S(p)` and has a smaller coefficient. [Lean declarations](ThetaDivisibleDiagonal.lean) · [Pinned definition and open conjectures](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean#L36-L95) · [Density-one lower bound](PRIME-DENSITY.md)

## Where the coefficient comes from

Write `w(u) = cot(πu/(2p))`. In the full cotangent expansion the sign is positive if the least representative of `v/u mod p` is odd. When `v=gu` with `g` odd, that representative is exactly `g`. For all other pairs, the sign is positive precisely when the least representative of `v/p mod u` is odd. Retaining the original weights and normalization `2/p` on the latter pairs gives `R(p)`, formalized as `offDiagonal p`. [Full expansion and reciprocal sign](ThetaCotangentTriangle.lean) · [Exact split](ThetaDivisibleDiagonal.lean)

Let `D(p)` be the contribution from all odd multiples `v=gu`. Replacing the product of the two cotangents by `(2p/π)²/(g u²)` costs at most `g` per pair before normalization. The first `n` positive odd integers sum to `n²`. The total error is therefore at most `(2/p) Σᵤ (p/u)² ≤ (π²/4)p` by the odd Basel sum. This estimate holds for every positive integer `p`. [Product error](ThetaReciprocalCutoff.lean) · [Diagonal estimate](ThetaDivisibleDiagonal.lean)

The harmonic proxy for `D(p)` is

```text
(8p/π²) Σ_{odd u<p} u⁻² Σ_{odd g, gu<p} g⁻¹.
```

The inner sum differs from `(1/2) log(p/u)` by at most 3. Replacing it by `(1/2) log p` adds a summable error once weighted by `u⁻²`, since `log u/u² ≪ u^(−3/2)`. The same majorant covers the omitted tail `u ≥ p`. Summing `u⁻²` over positive odd integers gives `π²/8`, so the coefficient of `p log p` is exactly one half. The proof also gives `D(p) = p Σ_{odd a<p} 1/a + O(p)`. [Harmonic and cotangent bounds](ThetaDivisibleDiagonal.lean)

## Scope and sources

OMA's existing reduction uses `M(p) = p Σ_{odd a<p} 1/a` and a pointwise hypothesis comparing `M(p)` with twice the original sum in its floor-sum form. The theorem here identifies a positive part of the Fourier expansion equal to that candidate up to linear error. Proving the pointwise hypothesis still requires a lower bound for the nondivisible pairs. The original paper gives lower bounds in §6 and treats a different asymptotic in §5. The DeepMind issue, OMA reductions and LTS solved record checked on 2026-11-28 yielded no matching estimate for this divisible part. [OMA reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5611) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [LTS-listed odd harmonic bound](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7126) · [Berndt, Bhat, Meyer, Xie and Zaharescu](https://arxiv.org/pdf/2501.03234v3)

The replay uses Lean 4.33.1 and the canonical source at `f606af160664c5a10952e9a957b100a1cd45bbeb`. The eleven public theorem reports added or exposed in this result contain only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the derivation and formalization. [Notebook replay command](../../README.md)
