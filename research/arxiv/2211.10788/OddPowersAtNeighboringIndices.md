# Proper powers at neighboring Fibonacci–Lucas indices

For `n ≥ 2`, write `Uₙ = Fₙ + Lₙ₊₁` and `Vₙ = Fₙ + Lₙ₋₁`. **If `UₙVₙ` is a proper power, then `6 ∣ n`.** More precisely, at any given physical index `n = m+2`, the product is a proper power if and only if both of the following hold.

1. The index is divisible by six.
2. Some prime `p ≥ 5` and natural number `y` satisfy `yᵖ + 1 = 11Fₙ²`.

These statements have no external Diophantine hypothesis. The index-one product is 12. At index six the product is `19·37`, so the index condition alone is insufficient. The main declarations are `Arxiv.«2211.10788».neighboring_proper_power_index` and `neighboring_proper_power_iff`. [Product proof](HosoyaProperPowerIndices.lean) · [Neighboring values and indexing](NeighboringPrimePairs.md)

## The odd-power equation

For arbitrary integers `f,y` and odd integers `k > 1`, the equation `yᵏ = 1 + 11f²` forces `f=0` and hence `y=1`. The Lean declaration `HosoyaOddNorm.odd_power_eq_one_add_eleven_square` proves `f=0`. This is a case of the classical equation of Nagell and Cohn. Cohn’s Theorem 1 gives the odd-base obstruction in terms of the class number of the imaginary quadratic field. For coefficient 11, an even base is excluded modulo eight. The proof here uses the notebook’s explicit Euclidean algorithm in the ring of integers of ℚ(√−11). [Norm proof](HosoyaOddNormPowers.lean) · [Euclidean division](LucasFibonacciOddCubes.lean) · [Cohn, Theorem 1](https://www.impan.pl/shop/en/publication/transaction/download/product/81995#page=1)

It suffices to take an odd prime exponent `p`. A solution has even `f`. The elements `1 ± f√−11` are coprime because a common divisor divides their sum 2 and the first element is 1 modulo 2. Their product is a `p`th power. The units are ±1, so `1 + f√−11 = wᵖ` for an algebraic integer `w`. For `p=3`, writing `w=(a+b√−11)/2` gives `a(a²−33b²)=8`. Thus `|a|≤8`, and reduction modulo 11 gives `a≡2`, forcing `a=2, b=0`.

For `p≠3`, the nonzero residues of the quadratic ring modulo 2 have order dividing three. Thus `w≡1` modulo 2, and `w=a+b√−11` with integral coordinates. Its odd-power real coordinate 1 is divisible by `a`. Reduction modulo 11 excludes `a=−1`. Now `a=1` and the residue condition makes `b` even.

The remaining trace obstruction works for every odd radicand `d`. If `z=1+2c√d`, successive squaring writes `z^(2·2ˢ)` as `1+4Tc²u + 4Tcv√d`, where `T=2ˢ` and `u` is odd. Raising this to an odd power preserves the odd coefficient of `4Tc²`. Decomposing `p−1` into a power of two times an odd number and multiplying back by `z` gives `Re(zᵖ)−1` as `4Tc²` times an odd integer. Its vanishing forces `c=0`. [Dyadic proof](HosoyaOddPowerTrace.lean)

## What remains for the product

The identity `UₙVₙ = 11Fₙ² − (−1)ⁿ` gives the equation above at odd indices. At an even index, if `Fₙ` is odd then the product is 2 modulo 4 and cannot be a proper power. Evenness of `Fₙ` forces `3 ∣ n` by the strong divisibility of Fibonacci numbers. The earlier unconditional square and cube exclusions leave exactly the prime exponents in the displayed criterion. The Bennett–Skinner input in the previous notebook result covers this remaining sign. [Product identity](NeighboringLucasFibonacciPrimes.lean) · [Square exclusion](HosoyaNeighborProductPowers.lean) · [Cube exclusion](CubeNormAtEighteen.md) · [Bennett and Skinner, Theorem 1.1](https://doi.org/10.4153/CJM-2004-002-2)

The pinned DeepMind declaration asks for infinitely many primes equal to an upper value. This proper-power obstruction leaves that question and the simultaneous neighboring-prime question open. Codex assisted with the formalization. The focused replay target is `HosoyaProperPowerIndices`. [Canonical declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Primary Fibonacci–Lucas paper](https://arxiv.org/abs/2211.10788) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/8156) · [Notebook replay](../../README.md#replay)
