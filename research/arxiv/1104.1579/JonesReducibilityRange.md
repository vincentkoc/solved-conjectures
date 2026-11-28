# A degree range in Jones’s polynomial reducibility conjecture

For an odd integer `t ≥ 3`, put `m = 2(2ᵗ+1)/3` and `Pⱼ(X) = Xʲ + … + X + m`. Jones’s Conjecture 4.1 takes `t = 2⌈(k+1)/2⌉+1` and predicts that among all degrees `j ≥ t−k` the polynomial is reducible over ℚ exactly when `j = t`. The Lean proof establishes two parts of this prediction. [Jones, Conjecture 4.1](https://arxiv.org/pdf/1104.1579#page=7) · [Lean proof](CunninghamJonesLinearFactors.lean)

| Hypotheses | Conclusion |
| --- | --- |
| `j ≥ 1` and `j(j+1) ≥ t` | The only possible rational root is −2, and it occurs exactly when `j = t`. |
| `(2ᵗ+1)/3` is prime and `2 ≤ j ≤ 2t−5` | `Pⱼ` is irreducible over ℚ exactly when `j ≠ t`. |

For example, `t = 11` gives `(2¹¹+1)/3 = 683`, a prime. The second theorem settles all degrees from 2 to 17 for this parameter, including six degrees after the prescribed factorization. The full conjecture also asks about higher-degree factors for arbitrarily large `j` and parameters with composite `(2ᵗ+1)/3`.

**Rational roots.** A rational root of the monic polynomial is an integer dividing `m`. All coefficients are positive, so write it as `−b` with `b > 0`. Multiplying the polynomial by `X−1` shows that `j` must be odd. Reduction modulo 2 then shows that `b` is even. The root equation becomes

```text
3 b^(j+1) + b = 2^(t+1)(b+1) + 2.
```

The choice `b = 2` is equivalent to `j = t`. If `b > 2`, the positive difference `b−2` is divisible by `2^(min(j,t)+1)`. Since `b ≤ m < 2ᵗ`, this first implies `j < t` and then `b−1 ≥ 2^(j+1)`. The root equation also gives `(b−1)ʲ ≤ m` because `(b+1)(b−1)ʲ ≤ b^(j+1)`. Together the inequalities force `j(j+1) < t`.

**Higher-degree factors.** If `j+5 ≤ 2t`, every complex root has absolute value greater than `√2`. Otherwise the sum of the absolute values of its positive powers through `j` would be less than `m`, and the polynomial could not vanish. Any monic integral factor of degree at least two therefore has constant term of absolute value greater than 2, by the product of its roots. If `m = 2p` with `p` prime, any factorization into monic integral factors has a factor whose constant term has absolute value at most 2. A nonconstant such factor must be linear. The root bound, positivity and the integral coefficients force its root to be −2. Gauss’s lemma transfers the result to rational polynomials.

The pinned DeepMind declarations concern prime integers under `q ↦ 2q ± 1`. The polynomial result leaves those infinitude questions open. Searches of open and closed DeepMind and Open Math Agents issues and pull requests and the Left to Solve solved records found no matching formalization of these bounds. The two declarations `CunninghamChain.jones_rational_root_iff` and `CunninghamChain.jones_irreducible_iff_in_range` use only `propext`, `Classical.choice`, and `Quot.sound`. Codex assisted with the proof. [Pinned integer predicates](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/4755) · [Left to Solve](https://lefttosolve.com/api/solved) · [Notebook replay](../../README.md#replay)
