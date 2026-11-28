# Large positive theta sums in every reduced progression

For every positive modulus `q`, every invertible residue `a` modulo `q`, and every real `ε > 0`, the primes satisfying both conditions below have **divergent reciprocal sum**.

```text
p ≡ a (mod q),    |S(p)/(p log p) − 1/2| < ε.
```

Here `S(p)` is the signed integer floor sum in the pinned DeepMind source. In particular, given any real `A` and any height `B`, there is a prime `p > B` in that progression with `S(p) > A p`. The theorem `frequently_positive_one_mod_eight` specializes this to `p % 8 = 1` and `0 < S p`. Berndt, Bhat, Meyer, Xie and Zaharescu ask for positivity at **every** prime greater than five and, in v3 Conjecture 3.3, eventual growth past every fixed linear bound. The pinned Lean statements ask for positivity at every odd prime (`conjecture_1_1`) and eventual growth past each natural multiple at all odd primes (`conjecture_4_4`). Those pointwise lower bounds remain open. [Lean declarations](ThetaPrimeProgressions.lean) · [Pinned definition and conjectures](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean#L36-L95) · [Paper, §3](https://arxiv.org/pdf/2501.03234v3#page=4)

## The two reciprocal sums

1. The preceding finite theorem bounds the number of exceptional primes up to `X` by `C(ε) X/(log X)²`. In the interval `[2^k, 2^(k+1))`, their reciprocal sum is at most `2C(ε)/((k+1) log 2)²`. Summing over `k` shows that **all** exceptional primes together have finite reciprocal mass. [Two-sided count](PRIME-ASYMPTOTIC.md) · [Previous landing](https://github.com/vincentkoc/solved-conjectures/pull/72)
2. The reciprocal sum over all primes in a reduced progression diverges by the classical Dirichlet argument. We derive this input from Mathlib’s lower bound for the von Mangoldt series restricted to the progression. Write `t = 1/(k+1)`. Multiplying the series at `1+t` by `t` gives a lower bound tending to `1/φ(q) > 0`. If the prime reciprocals in the class were summable, the scaled prime terms would be dominated by them, since `t log n ≤ n^t`. Mathlib supplies a summable majorant for the nonprime terms. Dominated convergence would give a limit of zero. [Mathlib lower bound](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/PrimesInAP.lean#L348-L352) · [Nonprime contribution](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/PrimesInAP.lean#L181-L189) · [Kedlaya, primes in arithmetic progressions](https://kskedlaya.org/ant/chap-primes-in-ap.html)

Removing the exceptional primes therefore leaves a divergent sum in every reduced class. Taking `ε = 1/4` and then `p > exp(4A)` gives the linear-growth conclusion. As an immediate consequence the good primes have relative harmonic density one in each class. The Lean declarations establish convergence of the exceptional series and divergence of the good series directly. [Proof](ThetaPrimeProgressions.lean)

## Scope and replay

The progression input is classical. The theta-specific consequence uses the earlier quantitative exceptional-prime bound. The checked DeepMind issue, OMA reductions and LTS results yielded no matching statement for the original signed sum in the 2026-11-28 search. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5611) · [LTS-listed odd harmonic lemma](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7126)

The scoped replay uses Lean 4.33.1, the pinned upstream source and fifteen local modules in dependency order. All seven new public theorem reports use only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the derivation and formalization. [Notebook replay command](../../README.md)
