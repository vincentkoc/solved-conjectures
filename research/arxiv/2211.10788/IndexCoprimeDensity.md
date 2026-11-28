# The density of indices coprime to their upper Hosoya value

Put Uₙ = Fₙ + Lₙ₊₁ = 3Fₙ + Fₙ₊₁. The proportion of positive indices n ≤ X for which gcd(n,Uₙ) = 1 has a limit δ, and **2/3 < δ ≤ 3/4**. Every prime Uₙ at a positive index passes this test because Uₙ > n. Some composite terms pass too, including U₇ = 60. The pinned DeepMind question about infinitely many distinct prime Uₙ remains open. [Density theorem and prime-value implication](LucasFibonacciIndexCoprimeDensity.lean) · [Pinned sequence and question](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Ching et al.](https://arxiv.org/abs/2211.10788)

Mastrostefano and Sanna already prove existence of the density for a general integral linear recurrence and a polynomial in the index. Their Theorem 1.4 applies here with the polynomial G(n) = n. Their argument separates the small-prime periodic conditions from the large-prime tail. Here the Fibonacci return ranks and a cofactor identity give explicit constants, a finite error bound, and the numerical interval for this sequence. [Mastrostefano and Sanna, Theorem 1.4 and §§2–3](https://doi.org/10.1017/S0004972718000606) · [Earlier local multiplicities](IndexCommonDivisors.md)

## A finite bound for missed common primes

Let K ≥ 64 and let X, P, T be natural numbers with X ≤ PT. The number of positive n ≤ X for which some prime p ≥ K² divides both n and Uₙ is at most

```text
13X/(6K) + P + 8T².
```

In particular X = L³, P = L², T = L gives the error 9L² in addition to the cutoff term 13L³/(6K). For p ≤ P, simultaneous hits occupy at most one index class modulo pRₚ, where Rₚ is the first positive Fibonacci index with p ∣ Fᵣ. This follows by dividing the index by p and using the return-rank identity on the resulting progression. Such a prime contributes at most X/(pRₚ) + 1 indices. [Counting theorem](HosoyaIndexGcdTail.lean) · [Return rank on a prime step](HosoyaPrimePowerIndices.lean)

For primes in a shell K² ≤ p < 4K² with Rₚ < 4K, group them by their common rank r. Every prime in a group divides Fᵣ ≤ 2ʳ and is at least 2¹², so the group contains at most r/12 primes. For ranks at least 4K, count the 3K² available integers in the shell. The shell contributes at most 13/(12K) to the sum of 1/(pRₚ). Doubling K and summing gives 13/(6K) for the whole tail. For p > P, write n = pt with 1 ≤ t ≤ T. The prime divides Uₜ(7Fₜ − Uₜ), a positive integer at most 2^(2t+6). Summing the resulting bound on its number of distinct prime factors gives 8T² possibilities. [Reciprocal-rank estimate](HosoyaReciprocalRankTail.lean) · [Large primes and small cofactors](HosoyaIndexTailFactors.lean) · [Frobenius cofactor identity](HosoyaPrimePowerCofactors.lean)

## Quantifying the coprimality test

For primes p < K² the joint divisibility predicate is periodic with period (K²+1)!. That integer is divisible by p and by Rₚ ≤ p+1. Thus the finite sieve has a computable mean, and its count through X differs from X times the mean by at most one period. With P = ⌊X/T⌋+1 the large-prime bound shows that these periodic tests approximate the full frequency arbitrarily well. This proves convergence and gives a finite-sample error for each choice of K and T. [Periodic approximation](HosoyaPeriodicIndexSieve.lean) · [Frequency estimate and convergence](HosoyaIndexGcdDensity.lean)

For K = 64 the finite certificate eliminates eight primes whose joint index-and-value class is empty. For the other primes below 4,096 it uses the smaller of Rₚ and 33 and rounds each reciprocal weight upwards to a millionth. The total is 298,854 millionths. Adding 13/384 and taking T = 4,096 gives an asymptotic upper bound below 1/3 for the noncoprime fraction. Conversely, all indices in classes 3, 4 and 10 modulo 12 have a common prime divisor, giving the upper bound 3/4 for δ. [Finite weight certificate](HosoyaSmallRankWeights.lean) · [Two-sided density bound](LucasFibonacciIndexCoprimeDensity.lean)

An independent prime-by-prime recurrence found 318 of the 564 primes below 4,096 hitting an index and its value together. The resulting residue classes agreed at every index through 180,000 with direct modular fast doubling and an integer gcd. Of these indices, 131,199 were coprime and 48,800 had a common prime below 4,096. One further index had only a larger common prime. Lean 4.33.1 rebuilt and independently replayed all 11 modules. The 37 named axiom audits used only standard axioms. To reproduce the formal verification, select `LucasFibonacciIndexCoprimeDensity` in the notebook runner. [Replay instructions](../../README.md#replay)
