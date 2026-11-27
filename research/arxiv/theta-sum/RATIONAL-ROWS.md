# Signed sums of long Hardy rows

For every real `C > 0` there is a height `H` such that every prime `p > 2H²` congruent to one modulo `8(H!)²` has a family of distinct Hardy rows with both of the following properties.

* Their signed sum exceeds `Cp`.
* The sum of the magnitudes of their negative rows also exceeds `Cp`.

Each such progression contains arbitrarily large primes, all congruent to one modulo eight. Write the rows as the paper's `S′(p−a,p)`, indexed by odd `a`. Every selected index satisfies `a ≥ (p−H)/H`. Thus, for any fixed `C`, the rows eventually lie beyond the short block of order `√p`. No uniform bound of the form `Kp` can hold for the total magnitude of the negative long rows. If `S(p) ≤ 0` on this progression, its complementary rows must have signed sum below `−Cp`. Positivity of the full sum remains open. [Checked declarations](ThetaRationalRows.lean) · [Canonical definitions and Conjecture 1.1](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean#L36-L64)

## The selected rows

Take all ordered pairs of distinct coprime odd integers `u,v ∈ [3,H]`. For each fraction `u/v` in the prime field, take the odd least representative `a` of the pair `{u/v,−u/v}`. The height bound `2H² < p` makes the resulting indices distinct. Indeed equality up to sign implies `uz ≡ ±wv (mod p)` for two reduced fractions `u/v,w/z`. The positive cross products have sum below `p`, so the fractions agree over the rationals. The bound on each index follows similarly from `av ≡ ±u (mod p)`. If `aH+H < p`, one obtains either `av = u`, impossible for a reduced fraction with `v ≥ 3`, or `av+u = 0`.

Let `s(x)` be +1 on odd least representatives of units and −1 on even ones, and set `R(t) = Σₓ s(x)s(tx)`. The Lean proof identifies `R(a) = S′(p−a,p)` for odd `a`, and the sum of all these rows is the pinned `S(p)`. [Earlier odd-representative identity](DIAGONAL.md)

## Exact row values and cancellation

If `p = 1+uvd`, then `R(u/v) = d`. To see this, multiply the summation variable by `v`. At `x=1,…,p−1`, the resulting product of signs is `(−1)^(⌊ux/p⌋+⌊vx/p⌋)`. Writing `x−1 = dt+r` with `0 ≤ r < d` makes the two floors equal to `⌊t/v⌋` and `⌊t/u⌋`. Since both denominators are odd, their sum has the same parity as `(t mod u)+(t mod v)`. The Chinese remainder theorem now gives a product of two alternating sums over odd-length intervals. Each is one, and each value of `t` occurs `d` times.

For `u < v`, the least representative of `u/v` is `1+(v−u)ud`, which is odd. Its reciprocal can have either parity. As `R(−t) = −R(t)`, the two selected rows together contribute either `0` or `2d`. This retains the negative rows in the signed sum. For example, at `p = 2521`, height seven gives six rows. Directly evaluating the upstream floor sum gives values `168, −168` from the pair `{3,5}`, `120, 120` from `{3,7}`, and `72, −72` from `{5,7}`. Here every required `uv` divides `p−1`, which suffices for the row calculation.

Write `H_L = 1 + 1/2 + ⋯ + 1/L`. Whenever `6L+1 ≤ H` and `p ≡ 1 (mod 8(H!)²)`, the pairs `{3,6j+1}` for `1 ≤ j ≤ L` contribute two positive rows each. They give a signed subtotal of at least `2(p−1)H_L/21` over the whole family. For `v=6j+5`, `0 ≤ j < L`, the least representative of `v/3` is even. Each odd lift therefore contributes `−(p−1)/(3v)`. These rows alone give negative magnitude at least `(p−1)H_L/18`. The divergence of the harmonic numbers gives both assertions for a fixed height depending on `C`.

## Comparison and verification

OMA's existing harmonic block bounds the first odd indices using floor pairing. The present family consists of long indices on explicit prime progressions and contains cancellations of both signs. Liu's short-interval means sum Hardy rows over pairs of numerators and inverses in fixed fractional intervals, with multiplicities. Here each original row is counted once. Live DeepMind and OMA issues and PRs and LTS solved records were checked on 2026-11-28. The searches found no matching long-row bound. [OMA harmonic block](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6519) · [DeepMind row reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [Liu, Theorem 1](https://www.emis.de/journals/AMAPN/vol28_1/28_01.pdf) · [LTS solved feed](https://lefttosolve.com/api/solved)

An exploratory lift of the earlier tangent-number congruence to modulus `p²` required coefficients up to `p(p−2)`. Direct coefficient recurrence has order `p⁴` arithmetic operations, compared with order `p²` for direct evaluation. The calculation supplied no bound on the balanced residue. The long-row estimates above use only finite sums, the common-grid identity and the existence of arbitrarily large primes congruent to one. [Earlier tangent congruence](TANGENT.md)

Independent replay rebuilt the canonical source at `f606af160664c5a10952e9a957b100a1cd45bbeb`, the diagonal dependency and this module using Lean 4.33.1. Both notebook modules passed `leanchecker -v`. Each of the seven public theorem reports lists only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the derivation and formalization. [Notebook replay](../../README.md)
