# Stretched-exponential bounds for exceptional primes

For every real `c < 1/2` there are positive constants `C_c, a_c` such that for every integer `X ≥ 2`,

```text
#{p ≤ X : p prime, S(p) ≤ c p log p} ≤ C_c X exp(−a_c √log X).
```

Taking `c = 0` counts all nonpositive values of the canonical signed theta sum, including zeros and those at primes congruent to one modulo eight. For each fixed positive tolerance the same type of bound holds for the two-sided event `|S(p)/(p log p) − 1/2| ≥ ε`. Dividing by the number of primes still gives a saving beyond every fixed power of `log X`. Positivity at **every** odd prime and the eventual linear lower bound at **all** odd primes remain open. [Finite two-sided and lower-tail declarations](ThetaPrimeConcentration.lean) · [Pinned floor sum and conjectures](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean#L36-L95)

The stronger uniform statement controls the absolute error `E(p) = S(p)/p − (log p)/2`. There are absolute constants `B,b > 0` such that simultaneously for all `X ≥ 2` and real `t ≥ 0`,

```text
#{p ≤ X : p prime, |E(p)| ≥ t} ≤ B X exp(−b √t).
```

In particular, for every fixed power `D > 0` there are `K,C > 0` such that at most `C X/(log X)^D` primes up to any `X ≥ 4` have `|E(p)| ≥ K(1+log log X)²`. The earlier prime mean-square theorem gave only `O(X/t²)` for an arbitrary absolute threshold. All constants here are existential. [Uniform tail and log-log window](ThetaPrimeConcentration.lean) · [Previous mean-square bound](PRIME-MEAN-SQUARE.md)

## Split by the original reduced modulus

In the rational cone for the off-diagonal, reduce each numerator and denominator by their common factor. Write `d` for the resulting denominator and `q` for the denominator of a Fourier frequency; then `d = qm`. Keep the scalar rows with `d ≤ T` and interpolate only the rows with `d > T`. The split is made before projection to frequencies. The estimate below holds for every integer `T ≥ 1` and for arbitrary numerator windows omitting `d = 1`, which belongs to the deterministic diagonal. [Primitive-row identity](ThetaReciprocalInversion.lean) · [Diagonal calculation](DIVISIBLE-DIAGONAL.md)

On a small row, the original scalar sign is supported on odd numerators coprime to `d`. For arguments coprime to `d`, the residues `w` and `2d−w` give opposite signs. Each complete period sums to zero. After the first period, summation by parts bounds the reciprocal-weighted remainder by one. The whole scalar row has magnitude at most `3H_d`, with `H_d` the harmonic number. The common-factor weights are bounded by the reciprocal-square series. Summing `H_d/d` up to `T` bounds the small part pointwise by `O(H_T²)`, uniformly in the numerator cutoffs. [Small-row bound](ThetaDenominatorTails.lean) · [Reflected periodic sums](ThetaUniformWindows.lean)

For a surviving large row, put `β = 1/128`. Since `T < qm`, the factor `T^β` costs at most `q^β m^β`. The harmonic divisor estimate for the projected row contributes `(1+log q)m^(−5/4)`. After paying the `m^β` factor the resulting exponent is `−159/128 < −1`; the sum over `m` still converges. Bounding `1+log q` by `129q^β` gives

```text
T^β ‖block at Fourier denominator q‖ ≤ A q^(1/64)/q.
```

Squaring and summing over `q ≥ Q` leaves both gains `T^(−1/64) Q^(−15/16)`, since the remaining series has exponent `−33/32`. The three-band large sieve therefore bounds the second moment of the large-row interpolation on all integers up to `N^64` by `O(N^64 T^(−1/64))`. [Coefficient and variance proofs](ThetaDenominatorTails.lean) · [Three-band estimate](ThetaReciprocalVariance.lean)

## Prime counts and thresholds

For primes in `[N^56,N^64]`, the preceding cone approximation with an odd numerator width comparable to `N` gives an absolute constant plus a constant times the cone norm as an upper bound for `|E(p)|`. If `|E(p)| ≥ A(1+log T)²` for sufficiently large absolute `A`, the small rows leave a large-row norm of at least one. The second moment counts all such primes in the band. For large `X`, taking `N = 1+⌊X^(1/64)⌋` covers `(X/2,X]` with `N^64 ≤ 2^64 X`. Induction on `X` sums the bound over successive halves. The finitely many small endpoints are absorbed into `A`. This gives `O(X T^(−1/64))` with one constant for every `T ≥ 1` and every endpoint. [Finite transfer](ThetaPrimeConcentration.lean)

Choosing `T = ⌈exp y⌉` turns a threshold `A(2+y)²` into a count `O(X exp(−y/64))`. The square-root exponential tail follows by solving for `y`. For a relative deviation, primes above `√X` have `log p ≥ (log X)/2`, and the lower primes contribute at most `⌊√X⌋+1`. The proof keeps the constants uniform down to `X = 2`. [Absolute and relative tails](ThetaPrimeConcentration.lean)

## Sources and replay

The original paper asks for pointwise positivity and for eventual lower growth in v3 Conjecture 3.3. Its asymptotic in §5 concerns the companion sum. Lägeler’s distribution theorem concerns phases of individual Hardy sums. Liu and Zhang’s moments average over numerators. The checked DeepMind issue, OMA reductions and LTS entries yielded no matching stretched-exponential exceptional count for the original signed aggregate in the 2026-11-28 search. [Paper](https://arxiv.org/pdf/2501.03234v3#page=4) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5611) · [LTS-listed lemma](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7126) · [Lägeler](https://arxiv.org/abs/2207.04828) · [Liu and Zhang](https://ir.library.osaka-u.ac.jp/repo/ouka/all/10379/1658ojm.pdf)

The scoped replay uses Lean 4.33.1, the pinned upstream source and eighteen local modules in dependency order. All fifteen new or newly exposed public statements report only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the derivation and Lean formalization. [Notebook replay command](../../README.md)
