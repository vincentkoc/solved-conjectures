# A Möbius formula for exact Hosoya gcd densities

Put Uₙ = Fₙ + Lₙ₊₁. For positive m,d and any nonnegative a, let δ(m,a,d) be the natural density, among all positive integers, of indices n ≡ a (mod m) with gcd(n,Uₙ) = d. The earlier proof established existence and characterized positivity. The formula here gives the individual terms and proves absolute convergence. At d = 1 the density measures a necessary condition for primality of Uₙ. DeepMind's declaration asks for infinitely many distinct primes equal to some Uₙ. That question remains open. [Main Lean theorem](HosoyaMobiusDensityFormula.lean) · [Earlier density theorem](ExactGcdDensities.md) · [Pinned conjecture](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Ching, Flórez, Luca, Mukherjee and Saunders](https://arxiv.org/abs/2211.10788)

## The coefficients

Let z(h) be the least positive k with h ∣ Fₖ, and set D = lcm(m,h,z(h)). For h ≥ 1 test the residues 0 ≤ t < D for t ≡ a (mod m), h ∣ t and h ∣ Uₜ. If one passes, set β(h) = 1/D. Otherwise set β(h) = 0. There can be at most one such residue. Once h ∣ Uₜ, the other indices carrying h as a value divisor are exactly the indices congruent to t modulo z(h). Intersecting with the other two congruences gives the coefficient. [Return rank](LucasFibonacciProgressionDivisors.lean) · [Single-class and coefficient theorems](HosoyaDivisibilityDensities.lean)

With μ the Möbius function, the density is

$$
  \delta(m,a,d)=\sum_{j=1}^{\infty}\mu(j)\,\beta(dj).
$$

For a positive integer B, the sum over j ∣ B alone is the density u of the following finite sieve. It accepts indices on the progression for which d ∣ gcd(n,Uₙ) and gcd(n,Uₙ)/d is coprime to B. For any K ≥ 64, if every prime below K² divides B, then u − 4/K ≤ δ(m,a,d) ≤ u. The proof counts the excluded excess gcds using the earlier large-prime estimate. The coefficient calculation can use a separate period for each divisor. The number of squarefree divisors can still be large. [Finite inversion](HosoyaMobiusDivisorSieve.lean) · [Interval and limit](HosoyaMobiusDensityFormula.lean)

For example take m = d = 1 and B = 42. The eight divisors give u = 31/42, equal to the count 124/168 over one common period. With m = 7, a = 0, d = 7 and B = 30, the finite sieve gives u = 1/84. These are finite-sieve values. The interval error bound applies only at its stated prime cutoff. [Earlier strict bounds on the unrestricted coprime density](ExactGcdDensities.md)

## Absolute convergence

Every term is bounded in absolute value by 1/lcm(j,z(j)). Sanna and Tron prove summability of this majorant in Lemma 3.2 for their formula for gcd(n,Fₙ). Their grouping by the largest prime factor also works here. The compatibility coefficients β above account for the shifted initial values U₀ = 1, U₁ = 4 and the progression. Mastrostefano and Sanna treat natural density for general recurrence–polynomial gcds. [Sanna and Tron, Lemma 3.2](https://iris.unito.it/bitstream/2318/1676271/1/SannaTron20180209.pdf) · [Mastrostefano and Sanna](https://doi.org/10.1017/S0004972718000606)

For largest prime p > 5 put r = z(p). Group the integers n in that block by g = gcd(n,r). Then n/(pg) is an integer with prime factors at most p, and lcm(n,r) = pr · n/(pg). Summing over g costs at most 2√r. The sum of reciprocals of the smooth cofactors is the finite prime Euler product. Applying Cauchy–Schwarz in dyadic prime intervals gives, for every sufficiently large K and every finite set of j with largest prime factor at least K²,

$$
 \sum_j \frac{1}{\operatorname{lcm}(j,z(j))}
 \le 64 e^4\,\frac{\log(2K)+4}{\sqrt K}.
$$

The smooth complement also has finite reciprocal mass. The absolute majorant therefore permits a limit over divisors of (K²)! in the finite inversion formula. [Smooth reciprocal sum](HosoyaSmoothHarmonicBound.lean) · [Largest-prime block](HosoyaLargestPrimeBlock.lean) · [Dyadic estimate](HosoyaLogRankShells.lean) · [Summability and tail](HosoyaRankLcmSummability.lean)

The main declarations are `exact_gcd_mobius_density`, `mobiusTerm_summable` and `divisorSum_interval` in `Arxiv.«2211.10788».IndexDivisors`. Independent modular recurrence arithmetic checked the single-class criterion for all 2,016 choices with 1 ≤ m ≤ 7, 0 ≤ a < m and 1 ≤ h ≤ 72 over two periods each. Eight signed finite sums matched direct counts. For n ≤ 3,000 a second calculation verified 2,928 largest-prime fiber identities and 429 block bounds. Lean 4.33.1 rebuilt and independently kernel-replayed all 41 modules. The 187 named axiom reports used only `propext`, `Classical.choice` and `Quot.sound`. Replay the module `HosoyaMobiusDensityFormula` with the notebook runner. [Replay instructions](../../README.md#replay)

The live source matched the pinned declaration. Searches of DeepMind and OMA issues and PRs and 10,511 DeepMind-source LTS solved records found the original issue and statement PR. No matching formalization of this shifted progression formula appeared in those searches. Codex assisted with the formalization. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/8156) · [OMA search](https://github.com/lefttosolve2/open-math-agents/issues?q=2211.10788) · [LTS records](https://lefttosolve.com/api/solved?source=deepmind)
