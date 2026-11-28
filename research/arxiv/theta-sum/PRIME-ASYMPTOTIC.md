# One half is the leading coefficient in prime density

For every real `ε > 0`, there exists `C(ε) > 0` such that for every integer `X ≥ 2`,

```text
#{p ≤ X : p prime, |S(p)/(p log p) − 1/2| ≥ ε} ≤ C(ε) X/(log X)².
```

Here `S(p)` is the signed integer double floor sum in the pinned source. Dividing by the number of primes up to `X` makes the exceptional proportion tend to zero. This gives both the upper and lower logarithmic scale, with leading coefficient one half. The proof gives an existential constant depending on the tolerance. Pointwise positivity and the eventual lower bound over **every** prime remain open. [Exact membership, finite bound and density limit](ThetaPrimeAsymptotic.lean) · [Pinned definition and conjectures](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean#L36-L95)

The finite bound also counts exceptions in each fixed reduced residue class. For instance, the classical prime number theorem in progressions gives `π(X;8,1) ∼ X/(4 log X)`, so the exceptional fraction within the primes `p ≡ 1 mod 8` tends to zero. The Lean density declaration uses all primes as its denominator. The progression count is a separate classical input. [Prime number theorem in arithmetic progressions](https://kskedlaya.org/ant/chap-primes-in-ap.html)

## The two cutoffs

In the full cotangent expansion use the odd indices `u,v < p` and weights `w(u) = cot(πu/(2p))`, with outer factor `2/p`. The pairs with `u | v` contribute `(p/2) log p + O(p)`. Write `R(p)` for the rest. On these remaining pairs the sign is determined by the parity of the least representative of `v/p modulo u`. [Exact diagonal and remainder](DIVISIBLE-DIAGONAL.md)

First discard denominators `u ≥ 2J+1`. At each fixed numerator, the field-quotient signs satisfy the earlier interval-discrepancy bound `D(p)`. Setting the multiples to zero costs at most one per divisor of `v`, hence at most `2⌊√p⌋` in any interval. Summation by parts against the decreasing cotangent weights gives total absolute error at most `2(D(p)+2⌊√p⌋) p H_{⌊p/2⌋}/(2J+1)`. Here `H_n` is the ordinary harmonic sum. [Denominator cutoff](ThetaNondivisibleCone.lean) · [Incomplete reciprocal discrepancy](ThetaReciprocalCutoff.lean)

Next fix an odd positive integer `K` and retain numerators `v < Ku`. In the tail starting at `Ku`, the reciprocal sign with multiples set to zero is periodic along the odd indices with period `u`. Negation reverses its sign, so each complete period sums to zero and every aligned prefix has absolute sum at most `u`. Summation by parts bounds one weighted tail by `u w(Ku) ≤ p/K`. Across the retained denominators this costs at most `2p H_J/K`. After linearizing the weights the rational cone sum is

```text
B(p,J,K) = Σ  sign(v/p mod u)/(uv),
           odd u < 2J, odd v < Ku, u ∤ v,
```

where the sign is positive on odd least representatives. For `J=N^52` and `N^56 ≤ p ≤ N^64`, uniformly for odd primes and `N ≥ max(2,K)`,

```text
|R(p) − (8p/π²) B(p,J,K)| ≤ 2300000 p + (2p/K)(1 + log p).
```

The fixed-width error can therefore use an arbitrarily small fraction of `p log p`. [Finite cone and its errors](ThetaNondivisibleCone.lean) · [Uniform transfer](ThetaPrimeAsymptotic.lean)

## Why the variance stays bounded

Write `u=gd` and `v=gw` in lowest terms. Divisibility corresponds exactly to `d=1`. Otherwise the numerator restriction becomes `w<Kd`, independent of `g`. Each odd common factor contributes `1/g²`. Fourier inversion on the reduced moduli now interpolates the rational cone exactly by a single function on all integers at the given scale. Assigning zero positive numerators to `d=1` removes the entire divisible part before taking the variance. [Window interpolation](ThetaReciprocalInversion.lean)

For a frequency of reduced denominator `q`, the contributing original moduli are `d=qm`. The projected vector for one numerator has Euclidean norm at most `τ(m)/m`. The numerator weights add to at most `H_{Kd} ≤ K H_d`. Thus the block norm is `O_K((1+log q)/q)`, and the primitive squared mass for denominators at least `Q` is `O_K(Q^(−15/16))`. Applying the three-band additive large sieve with the same `J` for every argument gives a total second moment `O_K(N^64)` on the integers up to `N^64`. [Projection and energy](ThetaReciprocalBlocks.lean) · [Large sieve](ThetaReciprocalLargeSieve.lean) · [Uniform variance](ThetaReciprocalVariance.lean)

Given `ε`, choose `K` with `2/K ≤ ε/4`. At sufficiently large scales, a deviation in the original `S(p)` forces the absolute value of the interpolating function to exceed a positive multiple of `ε log N`. Each exceptional prime in the interpolation range then costs a constant times `(log N)²` in the second moment. The integers below `N^56` and the gaps between successive 64th powers are accounted for in the finite count. Chebyshev's lower bound for the prime-counting function supplies the normalization. [Prime exception transfer](ThetaPrimeDensity.lean) · [Application to the canonical sum](ThetaPrimeAsymptotic.lean)

## Sources and replay

Berndt, Bhat, Meyer, Xie and Zaharescu discuss their numerical fits and propose the eventual two-sided inequalities of v3 Conjecture 3.3. Their separate asymptotic in §5 concerns the companion sum associated with `T`. OMA uses `p Σ_{odd a<p} 1/a` as a candidate main term in a pointwise lower-bound reduction. Its leading coefficient is already one half. Lägeler studies phases of individual Hardy sums over coprime pairs, and Liu and Zhang study even moments over numerators. The checked paper, DeepMind issue, OMA reductions and LTS records yielded no matching two-sided exceptional-prime bound for the **signed aggregate** `S(p)` in the 2026-11-28 search. [Paper, §3](https://arxiv.org/pdf/2501.03234v3#page=4) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5611) · [LTS-listed odd harmonic lemma](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7126) · [Lägeler](https://arxiv.org/abs/2207.04828) · [Liu and Zhang](https://ir.library.osaka-u.ac.jp/repo/ouka/all/10379/1658ojm.pdf)

The scoped replay uses Lean 4.33.1, the pinned canonical source at `f606af160664c5a10952e9a957b100a1cd45bbeb`, and the fourteen local modules in dependency order. All thirty new or newly exposed public theorem reports use only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the derivation and Lean formalization. [Notebook replay command](../../README.md)
