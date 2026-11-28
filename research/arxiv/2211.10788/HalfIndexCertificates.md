# Half-index primality certificates for the two neighbors

Let `U(n) = Fₙ + Lₙ₊₁` and `V(n) = Fₙ + Lₙ₋₁`. At each positive even index `2m`, the Fibonacci numbers `a = Fₘ` and `b = Fₘ₊₁` determine a factorization of each neighbor minus one. The larger factor suffices for a primality certificate for that neighbor. The certificate uses only the prime divisors of this factor. [Lean proof](LucasFibonacciHalfIndexCertificates.lean) · [Ching et al., p. 3](https://arxiv.org/pdf/2211.10788#page=3)

| Half index | `U(2m) − 1` | `V(2m) − 1` |
| --- | --- | --- |
| Even `m` | `(7b−a)a` | `(4a−b)(2b−a)` |
| Odd `m` | `(3a+b)(2b−a)` | `(7b−6a)a` |

These identities follow from Fibonacci doubling and Cassini’s identity `b²−ab−a² = (−1)ᵐ`. For a neighbor `N`, let `H` be the larger displayed factor. Then **`N` is prime exactly when there exists a residue `w` modulo `N`** such that

- `wᴴ = 1 mod N`, and
- for each prime `q ∣ H`, the residue `w^(H/q) − 1` is a unit modulo `N`.

For instance, at index 6, the upper neighbor is 37 and the lower is 19. The factorizations are `37−1 = 9·4` and `19−1 = 9·2`. The residues 7 modulo 37 and 4 modulo 19 both have ninth power 1 and their cubes differ from 1 by a unit. Only the prime 3 occurs in these certificate checks.

The order argument is a form of Pocklington’s primality criterion. If a witness exists, its reduction at every prime divisor `p` of `N` has order exactly `H`. Thus `p ≥ H+1`, but `(H+1)² > N` by the choice of the larger factor. A composite `N` would have a prime divisor at most `√N`. Conversely, for prime `N` its multiplicative group is cyclic, and `H ∣ N−1` gives a witness of order `H`. Checking a proposed witness still requires knowing the prime divisors of `H`. [Pocklington order criterion](https://flintlib.org/doc/algorithms/number-theory/primality-proving.html)

The even-index tests cover every simultaneous prime pair at indices `n ≥ 2`, since the previous residue obstruction forces each such `n` to be even. The index-one upper value is 4. The upper-diagonal test here applies at even indices only. The existence of infinitely many prime values on the upper diagonal, and of infinitely many simultaneous prime neighbors, both remain open. [Previous residue and semiprime criterion](NeighboringPrimePairs.md) · [Pinned DeepMind upper-diagonal question](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean)

The four result declarations in `Arxiv.«2211.10788»` are `prime_iff_order_certificate`, `halfIndexFactors_product`, `even_neighbor_prime_iff_halfIndex_certificate`, and `neighboring_primes_iff_halfIndex_certificates`. Each uses only `propext`, `Classical.choice`, and `Quot.sound`. The DeepMind issue and merged PR concern the upper-diagonal question. Searches of DeepMind and Open Math Agents issues and pull requests and Left to Solve’s solved records returned no matching half-index certificate. Codex assisted with the formalization. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [Canonical PR](https://github.com/google-deepmind/formal-conjectures/pull/8156) · [Left to Solve](https://lefttosolve.com/api/solved) · [Notebook replay](../../README.md#replay)
