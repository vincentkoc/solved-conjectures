# Lower growth of the theta sum on a density-one set of primes

For every real `c < 3/(4π²)`, there is a constant `C(c) > 0` such that, for every integer `X ≥ 2`,

```text
#{p ≤ X : p prime and S(p) ≤ c p log p} ≤ C(c) X/(log X)².
```

Here `S` is the pinned integer double floor sum. Chebyshev’s lower bound for `π(X)` makes the exceptional proportion among primes tend to zero. In particular, taking a positive `c` gives positivity and growth beyond every fixed multiple of `p` on a single density-one set. The constant in the count is existential. Individual exceptional primes and the eventual universal quantifier of pinned Conjecture 4.4 remain unresolved. The lower inequality of v3 Conjecture 3.3 has that same universal quantifier. [Main Lean theorems](ThetaPrimeDensity.lean) · [Pinned conjectures and definitions](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean#L36-L95) · [Berndt, Bhat, Meyer, Xie and Zaharescu, v3, §3](https://arxiv.org/pdf/2501.03234v3#page=4)

The finite exception bound also applies to any subset of primes. For primes congruent to 1 modulo 8, the classical prime number theorem in progressions gives `π(X;8,1) ∼ X/(4 log X)`. Dividing gives a vanishing exceptional proportion within that progression, hence infinitely many positive values there. The Lean theorem `prime_family_density` takes an eventual positive share of all primes as its explicit hypothesis. The progression estimate is an external classical input. [Lean family theorem](ThetaPrimeDensity.lean) · [Kedlaya, prime number theorem in arithmetic progressions](https://kskedlaya.org/ant/chap-primes-in-ap.html)

## Why a finite prime average works

The earlier triangle estimate gives `S(p) − R(p) ≥ (3/(4π²)) p log(p/6)`. Its finite cutoff bounds the error in replacing `R(p)` by `(8p/π²) B_J(p)`, where `B_J` sums the reciprocal parity sign with weights `1/(uv)` over odd `1 ≤ v < u < 2J`. Take `X = N^64` and the **same** `J = N^52` for every prime between `N^56` and `X`. The error on that interval is at most `2300000 p`. A fixed `c < 3/(4π²)` therefore forces `|B_J(p)| ≫_c log N` at each sufficiently large exceptional scale. [Triangle bound](COTANGENT-TRIANGLE.md) · [Finite cutoff](RECIPROCAL-CUTOFF.md)

Reduce each fraction `v/u = w/d` before extending its parity sign to all integers. For a unit argument `n mod d`, the sign is positive on odd least representatives of `w/n` and negative on even ones. Extend by zero on nonunits. An odd common factor `g` preserves the sign and contributes the weight `1/g²`. Finite Fourier inversion gives an extension `E_Y(n)`, with `Y = 2J`, that agrees exactly with `B_J(p)` for every prime `p > Y`. Negating a unit in any complete common period reverses the original rational cutoff, so its signed first moment on those units is exactly zero. [Parity and mean](ThetaReciprocalFibers.lean) · [Interpolation](ThetaReciprocalInversion.lean)

For an additive frequency of reduced denominator `q`, only moduli `d = qm` contribute. Inversion on units maps each residue fiber modulo `q` to another one. Möbius inversion for coprimality leaves one alternating progression for each divisor of `m` that contributes. Its signed sum has absolute value at most one. Thus each fiber has discrepancy at most `τ(m)`, and Parseval bounds the projected coefficient vector for one numerator by `τ(m)/m` in Euclidean norm. After summing the actual numerator and common-factor weights, the norm for denominator `q` is `O((1+log q)/q)`, uniformly in `Y`. The sum of squared coefficients over primitive frequencies with denominators at least `Q` is `O(Q^(-15/16))`. [Fiber estimate](ThetaReciprocalFibers.lean) · [Weighted coefficient bounds](ThetaReciprocalBlocks.lean)

For a band with denominators at most `D`, distinct reduced frequencies differ by at least `1/D²`. The elementary additive large sieve proved here costs `2(X + 2D² H_{D²})` for the interval `0 ≤ n < X`. The proof splits at frequency one half, bounds the off-diagonal geometric sums, and sums their reciprocal distances. Splitting the denominators at `N^28`, `N^44`, and `2N^52` and applying the squared-mass bound separately gives

```text
Σ_{0 ≤ n ≤ N^64} |E_{2N^52}(n)|² ≤ K N^64.
```

The constant `K` is independent of `N`. This direct proof permits a logarithmic factor in the sieve. Sharper classical additive large-sieve constants are available. [Elementary sieve](ThetaReciprocalLargeSieve.lean) · [Three-band variance](ThetaReciprocalVariance.lean) · [Montgomery and Vaughan](https://doi.org/10.1112/S0025579300004708)

Restrict the nonnegative second moment to exceptional primes. Each large one costs at least a constant times `(log N)²`, and at most `N^56` integers lie below the interpolation interval. Monotonicity of the count extends the bound between consecutive 64th powers. Cauchy–Schwarz separately bounds the mean absolute rational cutoff on primes `2N^52 < p ≤ N^64`, divided by **all** `π(N^64)` primes, by `O(√log(N^64))`. This supplies prime normalization without assuming cancellation in a signed prime sum. [Exception and first-moment bounds](ThetaPrimeDensity.lean)

## Prior results and verification

The original paper gives lower bounds in §6 and an asymptotic in §5 for a different sum associated to `T(k)`. Lägeler’s equidistribution theorem samples phases of individual Hardy sums over coprime pairs. Liu and Zhang study even moments over numerators. The live DeepMind issue reduces the full conjectures to an inequality for a remainder. A separate OMA reduction takes half the main term `p Σ_{a<p, a odd} 1/a` as a pointwise lower-bound hypothesis. The OMA proof listed as solved by LTS bounds the odd harmonic sum up to a square by twice the sum up to its root. The public sources and issue/PR searches checked on 2026-11-28 yielded no matching exceptional-prime estimate for the signed aggregate `S(p)`. [Original paper](https://arxiv.org/abs/2501.03234) · [Lägeler](https://arxiv.org/abs/2207.04828) · [Liu and Zhang](https://ir.library.osaka-u.ac.jp/repo/ouka/all/10379/1658ojm.pdf) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA main-term reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5611) · [OMA child](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7126) · [LTS solved records](https://lefttosolve.com/api/solved)

A fresh Lean 4.33.1 replay compiled the canonical source at `f606af160664c5a10952e9a957b100a1cd45bbeb` and all eleven local modules in the dependency chain. Independent kernel replay with `leanchecker` passed on all eleven. Every one of the 21 new public theorems prints only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the derivation and Lean formalization. [Notebook replay](../../README.md)
