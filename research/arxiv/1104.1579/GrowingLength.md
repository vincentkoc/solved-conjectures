# An unconditional bound for long Cunningham chains

For either of Jones’s recurrences, let `P(k,N)` count the natural seeds at most N whose first k terms are all prime. There is an absolute positive integer C such that, for every sufficiently large k and both signs,

```text
N ≥ (k+1)^(Ck)   implies   P(k,N) ≤ 4(N+1) exp(−k).
```

Both the cutoff and the estimate use the same C for all k and both recurrences. The fixed-length upper bound `Oₖ(N/(log N)ᵏ)` allows its implied constant and its starting point to depend on k. It therefore does not by itself yield this estimate when the requested length grows with N. [Lean proof](CunninghamGrowingLength.lean) · [Fixed-length sieve](SelbergCounts.md)

Equivalently for the counting application, there is an absolute `c > 0` with the following property. Set `L = c log N / log log N`. For all sufficiently large N and every integer `l ≥ L`, at most `4(N+1) exp(−L/2)` seeds have a prime prefix of length l. The same upper bound holds for the canonical exact-length predicate, which also requires the next term to be nonprime. Taking `l = ⌈L⌉` counts all seeds supporting at least L prime terms. The result is unconditional and permits exceptional seeds. Ford’s bound under a base-two Artin density hypothesis applies to every individual seed. Jones’s conjectured infinitude at each prescribed length remains open. [Pinned exact-length predicates](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean) · [Pointwise bound under Artin](ArtinLengthBound.md) · [Jones](https://arxiv.org/abs/1104.1579)

## Primes with k distinct forbidden residues

For an odd prime q, the number of forbidden seed residues is `min(k,ord_q(2))`, the same for both signs. Primes above k² with fewer than k forbidden residues have total reciprocal mass at most one. This follows because each such prime divides the product of the integers `2ⁱ−1` for `1 ≤ i ≤ k`. [Local root counts](BatemanHornCounts.md) · [Exceptional primes](SingularSeriesGrowth.md)

Write `E(z) = ∏_{p≤z} (1−1/p)⁻¹`. The elementary bounds `log(z+1) ≤ E(z) ≤ 2 exp(4) log z` hold for all sufficiently large z. Choose an absolute integer A large enough that `E(kᴬ)/E(k²) ≥ exp(6)` eventually. The bound `(1−1/p)⁻¹ ≤ exp(2/p)` gives reciprocal mass at least three in this interval. Discarding the exceptional primes leaves a subset Q of primes between k² and kᴬ with exactly k forbidden residues each and total reciprocal mass between one and two. Every prime in Q has multiplicative order at least k. [Euler-product estimates](CunninghamSingularSeriesGrowth.lean)

## Counting the survivors

For `q ∈ Q`, put `u(q)=k/q`. Then `k ≤ Σu(q) ≤ 2k`, so the fraction of surviving residues over a full period is at most `exp(−k)`. The full period may exceed the seed range. Instead truncate inclusion–exclusion after 16k terms. Bounding the next elementary symmetric sum by `2^(−16k−1) ∏(1+2u(q))` makes that truncation cost at most another `exp(−k)`.

The Chinese remainder theorem bounds the incomplete-period error by `(16k+1)(1+k(kᴬ+1))^(16k)`. Add the seeds up to kᴬ separately since a prime term can equal a sieving prime. Increasing C absorbs both errors into the asserted bound whenever `N ≥ (k+1)^(Ck)`. For the cutoff expressed in terms of N, use `k = ⌊L⌋` with `c = 1/(2C)`, then apply monotonicity in the requested length. [Finite Brun sieve](CunninghamBrunSieve.lean) · [Ford’s sieve notes](https://ford126.web.illinois.edu/sieve2023.pdf)

The three result declarations are `chain_full_root_band`, `primePrefixSeedCount_uniform_exponential` and `long_prefix_seed_exceptional_bound`. The proof also exposes the existing Bonferroni and Euler-product estimates as `brun_upper_residue_count` and `prime_euler_product_log_bounds`. Lean 4.33.1 compiled both pinned source files and five notebook modules from fresh output. All five notebook modules passed separate kernel replays. The 24 named axiom reports use only `propext`, `Classical.choice` and `Quot.sound`. [Notebook replay](../../README.md#replay)
