# The theta sum modulo its prime argument

One integral sequence determines `S(p) mod p` for every odd prime. Let `T_j` be the coefficients of the exponential generating series `tanh(t) − 1`, starting with `−1, 1, 0, −2, 0, 16`. Define

```text
D_n = Σ_{1 ≤ j < n} 2^(n−j) T_j² T_(n−j).
```

Then **`2 S(p) ≡ −D_(p−1) (mod p)`**. In particular, `p ∤ D_(p−1)` certifies `S(p) ≠ 0`. At 41 and 89 the [modulo-sixteen criterion](MOD-SIXTEEN.md) gives residue zero, while `D_40 ≡ 4 (mod 41)` and `D_88 ≡ 61 (mod 89)` exclude an integer zero. At 19, both `D_18` and `S(19) = 38` are divisible by 19. Divisibility alone leaves the integer sign undetermined. [Checked declarations](ThetaTangentResidue.lean) · [Pinned definition and conjecture](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean#L36-L64)

## Proof

Write `O = {1,3,…,p−2}` in the prime field, `M_j = Σ_{a∈O} a^j`, and let `s(u)` be +1 or −1 according to whether the least representative of a unit is odd or even. The geometric sum of `(u/c)^j` for `0 ≤ j < p−1` is −1 when `u=c` and zero otherwise. Summing this identity over `c ∈ O` gives the indicator of `O` with a minus sign. Removing the constant term using `2|O| ≡ −1 (mod p)` gives

```text
s(u) = −2 Σ_{1 ≤ j < p−1} u^j M_(p−1−j).
```

The [odd-representative identity](DIAGONAL.md) writes `S(p) = 2 Σ_{a,b∈O} s(ab)`. Substitution gives `S(p) = −4 Σ_j M_j² M_(p−1−j)` in the prime field.

It remains to remove the dependence of each moment on `p`. For `0 < k < p−1`, the sum of the `k`th powers of all units vanishes. The even representatives are exactly `O+1`. Expanding `Σ_{a∈O} [a^k+(a+1)^k]` by the binomial theorem therefore yields

```text
2 M_k = −Σ_{0 ≤ i < k} binom(k,i) M_i.
```

The sequence in the Lean proof uses the integral recurrence `T_0 = −1` and `T_k = −Σ_{i<k} binom(k,i) 2^(k−i−1) T_i`. In characteristic zero this is coefficient comparison in `(1+exp(2t))(tanh(t)−1) = −2`. In the prime field the recurrence and the initial value show by induction that `T_k = 2^(k+1) M_k` when `k < p−1`. In each term of `D_(p−1)`, the powers of two then multiply to `2^(2(p−1)+3) ≡ 8 (mod p)`. Comparing with the moment formula proves the congruence. [Maclaurin series for the hyperbolic tangent](https://dlmf.nist.gov/4.33.E3)

## Scope and verification

The public congruence, divisibility equivalence and nonvanishing criterion use the upstream integer `S`, `p.Prime` and `p % 2 = 1`. Lean formalizes the sequence by its integral recurrence. An independent numerical check used `(tanh t)′ = 1 − tanh² t` to generate the coefficients, and checked all odd primes through 400. The DeepMind and OMA issues and PRs and the LTS solved feed yielded no matching prime-modulus formula on 2026-11-28. [DeepMind row reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA finite reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7053) · [LTS solved records](https://lefttosolve.com/api/solved)

Independent replay compiled the canonical source at `f606af160664c5a10952e9a957b100a1cd45bbeb`, the diagonal identity and the new module with Lean 4.33.1, then checked both notebook modules with `leanchecker`. Each public theorem prints only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the derivation and formalization. [Notebook replay](../../README.md)
