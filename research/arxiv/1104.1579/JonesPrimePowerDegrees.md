# Jones’s polynomial in power-of-two degrees

For **every** odd parameter `t ≥ 3` in Jones’s Conjecture 4.1 and **every** exponent `a ≥ 0`, the polynomial `Pⱼ(X) = Xʲ + … + X + m` is irreducible over ℚ at degree `j = 2ᵃ`, where `m = 2(2ᵗ+1)/3`. This gives unbounded degrees for each parameter. The same proof works for every natural constant `m ≡ 2 (mod 4)`. For example, `t = 9` gives `m = 342` with composite odd part 171, and every degree 2, 4, 8, 16, 32, … is covered. [Jones, Conjecture 4.1](https://arxiv.org/pdf/1104.1579#page=7) · [Lean proof](CunninghamJonesPrimePowerDegrees.lean)

For `j = 2ᵃ ≥ 4`, reduction modulo 2 gives `Pⱼ = X(X−1)ʲ⁻¹`. Also `Pⱼ(1) = m+j ≡ 2 (mod 4)`. In any factorization into monic integral factors, at least one factor has odd value at 1. Its reduction is coprime to `X−1`, so it divides `X`. Monicity preserves its degree under reduction. If this factor were nonconstant, it would therefore give an integer root. For even `j`, pairing the powers in `Pⱼ(z)` gives `m + Σ z²ⁱ z(z+1) > 0` for every integer `z`. This excludes a linear factor. At degree two the same positivity already suffices, and degree one is immediate. For odd `t`, the integer `(2ᵗ+1)/3` is odd, as required.

Two tests using any prime `p` give further degrees.

| Degree and constant | Arithmetic test | Conclusion over ℚ |
| --- | --- | --- |
| `j = pᵃ`, `p ∣ m` | `p² ∤ m+j` and there is no integer root | `Pⱼ` is irreducible. At Jones’s constant, if `j ≥ 2` and `j(j+1) ≥ t`, the root classification gives irreducibility exactly when `j ≠ t` under the same divisibility test. |
| `j+1 = pᵃ`, `j > 0`, `m ≡ 1 (mod p)` | `p² ∤ m+j` | `Pⱼ` is irreducible. Here the whole reduction is `(X−1)ʲ`, so the factor whose value at 1 is a unit modulo `p` must be constant. |

For instance, when `t = 9` we have `m = 342 = 2·3²·19` and `m−1 = 341 = 11·31`. The tests prove irreducibility in every degree `19ᵃ`, `11ᵃ−1`, and `31ᵃ−1` for `a ≥ 2`. These are additional special cases. The reducibility classification for arbitrary degrees in Jones’s conjecture and the two pinned DeepMind infinitude questions for integer prime chains remain open. [Earlier rational-root classification](JonesReducibilityRange.md) · [Pinned DeepMind integer-chain predicates](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean)

The result declarations in `CunninghamChain` are `jones_prime_power_degree_irreducible`, `jones_prime_power_degree_iff`, `jones_pred_prime_power_degree_irreducible`, `dyadic_degree_irreducible`, and `jones_dyadic_degree_irreducible`. Each uses only `propext`, `Classical.choice`, and `Quot.sound`. Searches of DeepMind and Open Math Agents issues and PRs and Left to Solve’s solved records found the integer-chain issue and no matching formalization of these tests. Codex assisted with the formalization. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/4755) · [Left to Solve](https://lefttosolve.com/api/solved) · [Notebook replay](../../README.md#replay)
