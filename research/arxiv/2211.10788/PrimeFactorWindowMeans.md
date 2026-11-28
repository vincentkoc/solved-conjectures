# Prime-value counts and mean factor counts on the upper Hosoya diagonal

Write Uₙ = Fₙ + Lₙ₊₁ = 2Fₙ + Fₙ₊₂. **Every 2,520 consecutive indices starting at 6 or later contain at most 613 prime values.** The bound is unconditional. In particular, even the largest possible fraction of prime indices in a translated interval has limit superior at most 613/2520 as the interval length tends to infinity. The pinned question asks whether infinitely many distinct Uₙ are prime and remains open. [Periodic sieve theorem](HosoyaPeriodicPrimeSieve.lean) · [Pinned definition and question](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean)

There is also a conditional bound for the mean number of distinct prime factors. Fix an index progression r+dt. Suppose the primes dividing at least one of its terms have relative natural density δ among all primes. For every 0 ≤ c < δ and all sufficiently large H,

```text
(1/H) ∑_{0 ≤ i < H} ω(U_{r+d(a+i)}) ≥ c log log(H+1)    for every start a ≥ 0.
```

Here ω(1) = 0. For the complete sequence, Moree and Stevenhagen prove the density hypothesis under GRH with δ ≈ 0.577470679956. Their sequence starts 3, 1, 4, 5, 9, while U starts 1, 4, 5, 9. The omitted term 3 already divides 9. The Lean theorem takes the relative density as its explicit input. The published GRH result supplies this input for r = 0, d = 1. The argument bounds a mean and does not settle how often a single term is prime. [Mean factor theorem](LucasFibonacciMeanFactors.lean) · [Moree and Stevenhagen, main theorem](https://arxiv.org/pdf/math/9912253#page=2)

## The periodic prime-value sieve

For positive D the sequence gcd(Uₙ,F_D) is periodic in n with period D. Indeed, every divisor of F_D divides Uₙ₊ᴰ exactly when it divides Uₙ. Once Uₙ > F_D, primality requires gcd(Uₙ,F_D) = 1. Thus counting the coprime residues in one period gives a bound at every translated block. [General period bound](HosoyaPeriodicPrimeSieve.lean) · [Divisibility under shifts](LucasFibonacciPrimePowerLifts.lean)

For D = 2520, eleven primes suffice. Each row satisfies p | F_R, p | Uₜ and R | D, so its prime divides every Uₙ with n ≡ t mod R.

| p | 2 | 3 | 5 | 7 | 19 | 23 | 31 | 71 | 83 | 181 | 631 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| R | 3 | 4 | 5 | 8 | 18 | 24 | 30 | 70 | 84 | 90 | 630 |
| t | 1 | 3 | 2 | 4 | 12 | 5 | 23 | 45 | 48 | 36 | 95 |

Exactly 613 residues avoid these eleven obstructions. U₁₂ = 665 already exceeds every listed prime, and the proof checks indices 6 through 11 separately. Counting complete blocks and one remainder gives the stated upper density. Independent arithmetic also found that the eleven primes give the same survivors as using the full gcd with F₂₅₂₀. Ching et al. give sieves for the determinant Hosoya triangle and report prime searches through index 80,000. The bound above applies to every translated block on their chosen diagonal. [Finite certificate](HosoyaPeriodicPrimeSieve.lean) · [Ching et al., introduction and §4](https://arxiv.org/abs/2211.10788)

## Counting distinct factors

For every prime p, the first positive return R with p | F_{dR} satisfies R ≤ p+1. Away from 5, Frobenius fixes or exchanges the two roots of X²−X−1, giving a Fibonacci return at p−1 or p+1. At 5 one can take 5. Multiplying the return index by d preserves divisibility. If p divides a value on the progression, periodicity therefore gives a hit in every p+1 consecutive parameters. Double counting prime incidences gives the unconditional inequality

```text
∑_{p ∈ S} ⌊H/(p+1)⌋ ≤ ∑_{0 ≤ i < H} ω(U_{r+d(a+i)}),
```

for every finite set S of primes dividing terms somewhere on the progression. Take S to consist of all such primes through H. Division by H and rounding cost at most two in the mean. [Return ranks](HosoyaPrimePowerIndices.lean) · [Finite-window incidence bound](HosoyaDivisorWindowCounts.lean)

An eventual lower bound c on their relative frequency transfers, by partial summation, to a lower bound c times the reciprocal sum over all primes, up to an additive constant. The finite Euler product over primes through H dominates the harmonic sum through H. Taking logarithms and bounding the telescoping error gives ∑_{p≤H} 1/(p+1) ≥ log log(H+1) − 2. Starting with a coefficient strictly between c and δ absorbs both constant errors uniformly in a. [Euler-product estimate](HosoyaPrimeHarmonicBounds.lean) · [Density transfer](LucasFibonacciMeanFactors.lean)

Independent modular recurrences checked 3,000 prime/progression combinations for primes below 700, including constant progressions. The 1,005 combinations with a hit passed all 16,080 translated-window tests. A separate gcd enumeration verified the 613 survivors and all 2,520 rotations. Lean 4.33.1 rebuilt ten notebook modules in clean output and independently replayed all ten. All 30 named axiom reports used only standard axioms. [Kernel replay instructions](../../README.md#replay)
