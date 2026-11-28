# A rational cutoff for the theta sign obstruction

Let `p` be an odd prime. The cotangent decomposition gives `S(p) = U(p) + R(p)` with `U(p) ≥ 3p log(p/6)/(4π²)`. Fix any real `3/4 < α < 1` and define the rational number

```text
Bα(p) = Σ_{1 ≤ v < u ≤ p^α, u,v odd} s_u(v p̄)/(uv),
```

where `p̄` is the inverse of `p` modulo `u` and `s_u` is +1 on odd least residues and −1 on even least residues. Then **`R(p) = (8p/π²) Bα(p) + o(p)`** along the primes. Thus a summation over smaller odd moduli, with rational arithmetic throughout, recovers the complementary triangle to error below the linear scale. At `α = 7/8` the double sum has `O(p^(7/4))` terms. [Lean proof](ThetaReciprocalCutoff.lean) · [Cotangent decomposition](COTANGENT-TRIANGLE.md)

For every odd prime the error is at most `152 p^r (log p)³`, where `r = max(7/4−α, 2α−1)`. Taking `α = 7/8` gives `r = 7/8`. Balancing the two errors at `α = 11/12` gives `r = 5/6`. The count of allowable denominators in Lean is exactly `(⌊p^α⌋+1)/2`.

If some fixed `b < 3/32` satisfies `Bα(p) ≥ −b log p` for every sufficiently large odd prime, then for every natural `n` one has `n p < S(p)` at every sufficiently large odd prime. The theorem `growth_of_rationalPrefix` has the quantifiers of pinned Conjecture 4.4. The lower bound on `Bα` remains a hypothesis. Positivity of the full sum remains open. [Pinned source](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean#L36-L95) · [Paper, v3 Conjecture 3.3](https://arxiv.org/pdf/2501.03234v3#page=4)

## Two finite errors

Write `H = H_⌊p/2⌋` and `D = 4p^(3/4)(1+H)²`. For a cutoff at the first `J ≤ ⌊p/2⌋` odd denominators, the total error relative to the rational approximation is at most

```text
2 D p H/(2J+1) + 4 J² H_J/p.
```

The first term bounds the signed contribution of large denominators. For any nonzero numerator modulo `p`, the signed sum of the quotient parities over any step-two denominator progression contained in `[1,p−1]` has absolute value at most `D`. Fourier completion uses a Kloosterman sum `K(a,b) = Σ_{x≠0} e_p(ax+b/x)`. The parity transform vanishes at zero frequency. At the other frequencies the proof uses the classical elementary estimate `|K(a,b)| ≤ 2p^(3/4)` for `b ≠ 0`. Partial summation against the decreasing cotangent weights gives the stated tail bound. [Kloosterman, Acta Mathematica 49, pp. 407–464](https://doi.org/10.1007/BF02564120)

The finite proof of the Kloosterman estimate uses `Σ_b |K(a,b)|² = p(p−1)`. In the square of `K(a,b)`, substitute `y = tx`. The term at `t = −1` is `p−1`. Each other term is `K(a,b(1+t)(1+t⁻¹))`. For nonzero `b` a parameter has at most two preimages, since equal values force `s = t` or `s = t⁻¹`. Cauchy–Schwarz now gives the three-quarter-power estimate.

The second error bounds linearization on the retained triangle. For `x = πu/(2p)` one has `0 ≤ 1/x−cot x ≤ x/2` from the elementary sine and cosine bounds. For `v ≤ u`, replacing the product of the two cotangents by `4p²/(π²uv)` therefore costs at most `u/v`. Summing up to the cutoff gives `4J² H_J/p` after normalization.

As an independent numerical check at `α = 7/8`, the exact rational sums round to `Bα(41) ≈ −0.1230497`, `Bα(73) ≈ 0.4756091` and `Bα(1009) ≈ 0.8773852`. The directly evaluated normalized discrepancies `R(p)/p − 8Bα(p)/π²` are approximately `−0.058287`, `0.022539` and `−0.001827`, respectively.

## Prior work and replay

The three-quarter-power estimate is classical. This proof applies it to a uniform interval discrepancy and then to the specific remainder of the canonical theta sum. The DeepMind issue gives a signed row-discrepancy reduction. OMA addresses finite verification and a short-row harmonic estimate. The live DeepMind, OMA and LTS records checked on 2026-11-28 contained no matching sublinear rational cutoff. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA harmonic reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6519) · [LTS solved records](https://lefttosolve.com/api/solved)

Independent replay compiled the canonical source at `f606af160664c5a10952e9a957b100a1cd45bbeb` and five notebook modules with Lean 4.33.1. The seven public cutoff theorems and eight shared helper theorems print only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the derivation and formalization. [Notebook replay](../../README.md)
