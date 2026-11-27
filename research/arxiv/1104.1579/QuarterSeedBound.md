# A quarter-seed bound for Cunningham chains

Let `p` start an exact length-`k` chain in either of Jones’s recurrences. Then **`4k < p`**, with precisely the following exceptions. The pairs are (seed, exact length).

| Recurrence | All exceptions |
| --- | --- |
| First kind, `t ↦ 2t+1` | (2,5), (3,2), (5,4), (11,3) |
| Second kind, `t ↦ 2t−1` | (2,3), (3,2), (7,2) |

Both equivalences use the original prime-prefix and nonprime stopping-term predicates. In particular, the bound holds for **every prime seed greater than 11**. Kanado’s Remark 1.5 gives `k < p/2` for both kinds when `p ≥ 7`. The bound proved here concerns chain length for a given seed. Jones’s conjectures on infinitude of seeds at prescribed lengths remain open. [Lean proof](CunninghamLocalPeriods.lean) · [original predicates](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean) · [Jones, §1](https://arxiv.org/pdf/1104.1579#page=2) · [Kanado, Remark 1.5](https://arxiv.org/pdf/2205.07650#page=2)

**Local test.** Let `q` be any odd prime and `d` the multiplicative order of 2 modulo `q`. Write `s = p+1` for the first kind and `s = 1−p` for the second kind, with positive seed in the latter case. Then `q` divides at least one of the first `d` terms exactly when `sᵈ ≡ 1 (mod q)`: at index `i`, divisibility means `2ⁱs ≡ 1 (mod q)`. The `d`th roots of unity are precisely the powers of 2 in this field. If `p > q`, every term exceeds `q`, so a hit forces `k < d ≤ q−1`. Stones’s primitive-root obstruction is a related result for the case `d = q−1`. [Stones, Theorem 2](https://arxiv.org/pdf/0908.2166#page=2)

**First kind.** For `p > 40`, write `p+1 = 2ᵉ a` with `a` odd and `e ≥ 1`. If `a` is 1 or 3, the test with `q = 5` gives `k < 4`. Otherwise take the largest power of two `2ʲ ≤ a−2`. The remainder `m = a−2ʲ` is odd, exceeds one, and satisfies `2m ≤ a+1`. For any prime factor `q` of `m`, the shifted seed is `2ᵉ⁺ʲ` modulo `q`. Consequently `k ≤ q−2`, which gives the claimed bound.

**Second kind.** Write `p−1 = 2ᵉ a` with `a` odd and `e ≥ 1`. An odd prime `q ∣ a+1` gives `1−p ≡ 2ᵉ (mod q)` and `2q ≤ a+1`, so again `k ≤ q−2`. It remains to consider `a+1 = 2ʲ`. If `4k ≥ p > 40`, the local test at 11 forces `11 ∣ a`, since 2 has order 10 modulo 11. Hence `10 ∣ j`. Now `a+2 = 2ʲ+1` is composite: primality would force `j` to be a power of two. Its smallest prime factor `q` is odd and satisfies `2q ≤ a+2`. Since `−a ≡ 2 (mod q)`, this gives the same contradiction. The small-seed check verifies the first nonprime term for each prime `p ≤ 40` and proves all seven listed exceptional chains exist.

In namespace `CunninghamChain` the bound declarations are `firstKind_quarter_exceptions` and `secondKind_quarter_exceptions`. The local tests are `firstKind_dvd_in_period_iff` and `secondKind_dvd_in_period_iff`. The [notebook replay](../../README.md#replay) checks all four axiom reports with Lean 4.33.1.

Live searches of open and closed DeepMind and OMA issues and PRs covered the paper identifiers, the order of 2, and the length bound. The DeepMind results concerned the original statements. The OMA reductions split off length one. No matching formalization of the quarter-seed bound appeared in these searches or in the LTS solved records. Codex assisted with the formalization. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/4755) · [first-kind OMA reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8693) · [second-kind OMA reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8706) · [LTS solved records](https://lefttosolve.com/api/solved)
