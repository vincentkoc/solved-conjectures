# A finite test for unbounded Lucas–Fibonacci valuations

Fix a prime `p`, a starting index `r ≥ 0`, and an index step `d > 0`. Set `U(n) = 2Fₙ + Fₙ₊₂`. Define `e` to be the least positive `t` such that `p² ∣ F_{dt}`, and put `a = vₚ(F_{de})`. Then **arbitrarily high powers of `p` divide terms on the progression if and only if one of its first `e` terms is divisible by `pᵃ`**. Each power can occur at a different index. The criterion includes 2, 5 and 11 and assumes no conjecture about exceptional Fibonacci primes. [Lean proof](LucasFibonacciPrimePowerLifts.lean) · [Fibonacci return rank](ProgressionDivisors.md) · [Canonical upper diagonal](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean)

Two examples distinguish the outcomes. For `p=2,d=1` the return modulo 4 is at `e=6` and `F₆=8`. The first six upper-diagonal values are 1, 4, 5, 9, 14 and 23. None is divisible by 8, and the proof rules out divisibility by 8 at every index. For `p=3`, `U(3)=9` and `F₁₂=144` are both divisible by 9, while `27 ∤ F₁₂`. For every `b ≥ 0`, some `t < 3ᵇ` satisfies `3ᵇ⁺² ∣ U(3+12t)`.

## How a hit lifts

Suppose `m > 0`, `p ∣ m`, `m ∣ U(s)` and `m ∣ Fⱼ`. Put `A = Fⱼ₊₁−Fⱼ`, `B = Fⱼ/m` and `X = U(s)/m`. The next-level condition is the affine congruence

```text
pm ∣ U(s+jt)   ⇔   A X + t B U(s+1) ≡ 0 (mod p).
```

Both `A` and `U(s+1)` are units modulo `p` by consecutive-term coprimality. If `pm ∤ Fⱼ`, exactly one residue of `t` lifts. If `pm ∣ Fⱼ`, every residue lifts when `pm ∣ U(s)`, and none lifts otherwise. The corresponding Fibonacci return rank for modulus `pm` stays fixed or multiplies by `p` according to whether the old return already vanishes modulo `pm`.

For the finite test, `m=pᵃ` contains `p²` and `F_{de}/m` is a unit modulo `p`. The normalized recurrence can therefore be read modulo `p²`. It shows that replacing the step `j` by `pj` raises the Fibonacci valuation by exactly one. Iterating constructs a hit at every higher level. In the reverse direction, divisibility by `m` is periodic in progression steps modulo `e`, so any hit at this level yields one among the first `e` terms. Chavoya, Lucero and Reynolds study prime-adic valuations for a different generalized Fibonacci sequence, `Fₙ+2Lₙ`. The criterion here uses the initial pair `1,4` of the pinned problem. [Chavoya, Lucero and Reynolds, pp. 91–92](https://slmath-production-assets.sfo3.digitaloceanspaces.com/system/cms/files/81/files/original/Research_Reports_2014_MSRI-UP_%28Single_File%29.pdf) · [Ching et al., introduction](https://arxiv.org/pdf/2211.10788#page=3)

The five exported declarations in `Arxiv.«2211.10788»` are `unbounded_prime_powers_iff_finite_test`, `prime_mul_dvd_lucasFibonacciSum_iff`, `prime_mul_lifts_on_class`, `fibonacciStepRank_prime_mul` and `eight_excluded_three_unbounded`. Each uses only `propext`, `Classical.choice` and `Quot.sound`. Searches of open and closed DeepMind and OMA issues and PRs and the LTS solved records returned no matching formalization. The upstream infinitude of prime values remains open. Codex assisted with the proof. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [LTS solved records](https://lefttosolve.com/api/solved) · [Notebook replay](../../README.md#replay)
