# Densities of exact index–value gcds in progressions

Let Uₙ = Fₙ + Lₙ₊₁. For positive m and d and any a, consider the positive indices n ≡ a (mod m) with gcd(n,Uₙ) = d. Their natural density δ exists, measured among all positive integers. It is positive precisely when the earlier finite test finds a witness. For d = 1 and no restriction on n, the density lies strictly between 2/3 and 31/42. Index–value coprimality is necessary for primality of Uₙ. The pinned conjecture asking for infinitely many distinct prime values remains open. [Density decision](LucasFibonacciExactGcdDensities.lean) · [Finite test](ExactIndexGcdSpectrum.md) · [Pinned conjecture](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Ching, Flórez, Luca, Mukherjee and Saunders](https://arxiv.org/abs/2211.10788)

Mastrostefano and Sanna give general density existence results for gcds of linear recurrences and polynomial values. Sanna and Tron prove a positivity criterion and a series formula for gcd(n,Fₙ). Here the recurrence starts at U₀ = 1 and U₁ = 4. The Lean bounds below give a finite rational approximation in each prescribed progression and a uniform lower bound from any realizing residue. [Mastrostefano and Sanna](https://doi.org/10.1017/S0004972718000606) · [Sanna and Tron](https://doi.org/10.1016/j.indag.2018.03.002)

## Computing an interval for the density

Fix an integer K ≥ 64. Choose any positive A with A ∣ F_A such that m, d and every dp for primes p < K² divide A. Among the residues 0 ≤ t < A, count those with t ≡ a (mod m) and gcd(A,gcd(t,Uₜ)) = d. Write u for this count divided by A. Then

```text
u − 4/K ≤ δ ≤ u.
```

The truncated gcd is periodic. It accepts every true witness. A false positive has actual gcd divisible by dp for some prime p. If p < K², the truncated gcd would already include dp. The remaining indices fall under the earlier large-common-prime estimate. Its limiting error is at most 4/K. At finite X the absolute difference between the exact frequency and u is at most 4/K + (A+1+8K²)/X. This proves convergence by the Cauchy criterion. The even factorial A = (2(max(m,d(K²+1))+2))! always works, so the rational interval has arbitrarily small prescribed width in principle. The factorial makes direct enumeration impractical even at the initial cutoff. [Finite overcount](HosoyaExactGcdPeriodicSieve.lean) · [Frequency limit](HosoyaExactGcdFrequency.lean) · [Rational endpoints](HosoyaExactGcdDensityApproximation.lean) · [Large-prime estimate](IndexCoprimeDensity.md)

## Positive mass from one witness

For this bound A only needs to satisfy A > 0, A ∣ F_A and m ∣ A. Suppose some t < A realizes the truncated gcd d and t ≡ a (mod m). Put g = gcd(t,A), L = A/g, and h = t/g. Select indices n = gq with q ≡ h (mod L), excluding primes up to K² from q. Since gcd(h,L) = 1, primes dividing L are already excluded. For the product P of the remaining primes up to K², the Chinese remainder theorem gives φ(P) eligible residues modulo AP for n. Every excess common divisor forces a large prime dividing both q and Uₙ. Subtracting the same large-prime error yields δ ≥ φ(P)/(AP) − 4/K. [Residue count](HosoyaRoughCofactorResidues.lean) · [Density inequality](HosoyaExactGcdMassBound.lean)

The earlier Euler-product estimate gives φ(P)/P ≥ 1/(2 exp(4) log(K²)) for all sufficiently large K, uniformly in L. Choosing K = (BA)² gives a universal integer B ≥ 2 for which every realizing residue certifies

```text
δ ≥ 1 / (16 exp(4) A log(BA)).
```

The theorem proves existence of B. Its value is unnecessary for deciding positivity, which uses only the finite gcd test. [Totient bound](HosoyaRoughCofactorMass.lean) · [Euler product](../1104.1579/CunninghamSingularSeriesGrowth.lean) · [Uniform lower bound](HosoyaExactGcdDensityLower.lean)

## The coprimality sieve

Modulo 12, exactly nine classes have positive density of indices coprime to Uₙ. The exceptions are 3, 4 and 10. Modulo 168, exactly 124 residues pass the truncated coprimality test. The exact gcd-19 set also passes this sieve because 19 is coprime to 168. The witness gcd(228,U₂₂₈) = 19 gives this disjoint set positive density, making the upper bound 124/168 = 31/42 strict. The earlier lower bound gives 2/3 < δ. [Class and strict-density theorems](HosoyaCoprimeDensityClasses.lean) · [Earlier lower bound](IndexCoprimeDensity.md)

Independent integer arithmetic through n = 240,000 counted 174,930 coprime indices and 674 with exact gcd 19. Replay `HosoyaCoprimeDensityClasses` to check the proof and its dependencies. [Replay instructions](../../README.md#replay)
