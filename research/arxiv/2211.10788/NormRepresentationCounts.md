# Prime values and representations of discriminant −11

Write U(n) = Fₙ + Lₙ₊₁ for the upper Hosoya diagonal, and let R(v) count **all ordered integer pairs** (x,y) satisfying x²+xy+3y²=v. At every index n, U(n) is prime if and only if R(U(n))=4 and at least one pair has coprime coordinates. This gives a finite test because 4v=(2x+y)²+11y². The pinned question asks whether infinitely many distinct primes occur. The criterion applies pointwise and leaves this infinitude open. [Lean declaration](LucasFibonacciNormRepresentations.lean) · [Pinned question](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Ching et al., introduction](https://arxiv.org/abs/2211.10788)

At index 13 the distinction is visible inside the sequence. U(13)=1076=4·269. Its four pairs are ±(26,8) and ±(34,−8). All have even coordinates. The declaration `four_representations_at_composite_upper_value` verifies the value, the count and the absence of a primitive pair.

## Counting the representations

For every positive v coprime to 11 that has a primitive representation, R(v)=2τ(v), where τ counts positive divisors. This specializes the classical representation formula for the principal form of discriminant −11. The Lean proof derives the count from the norm in ℤ[(1+√−11)/2]. [Hardy and Williams, equation (1.7)](https://people.math.carleton.ca/~williams/papers/pdf/160.pdf) · [Vepkhvadze, discriminant −11](https://www.viam.science.tsu.ge/enl_ses/vol38/Vepkhvadze.pdf) · [Euclidean division in the quadratic ring](LucasFibonacciOddCubes.lean)

Let z have norm v and coprime coordinates. Since 11 does not divide v, z is coprime to its conjugate. Each positive divisor d of v is the norm of a factor s of z. If z=su, the element s·conj(u) has norm v. For each d this gives exactly one pair of opposite elements, and every element of norm v occurs this way. The exclusion of 11 matters. At v=11 the primitive pair (−1,2) has norm 11, but the only representations are this pair and its negative.

For positive v which is a nonzero square modulo 11, every prime v has a primitive representation. Quadratic reciprocity gives a square root of −11 modulo v, and factorization in the quadratic ring gives an element of norm v. Conversely, for a primitively represented v, the count is four precisely when τ(v)=2. The upper recurrence gives U(n)≡4ⁿ (mod 11), so the two implications apply at every upper index.

## Both diagonals at odd indices

For each m≥0, take v to be U(2m+1) or the lower neighbor at physical index 2m+3. If v is odd, R(v)=2τ(v). If v is even, R(v)=2τ(v/4). The omitted initial lower value is 3; its primitive pair (0,1) gives R(3)=4 by the same general count. [Shared Fibonacci form witnesses](LucasFibonacciOddCubes.lean) · [Lower indexing convention](NeighboringLucasFibonacciPrimes.lean)

The doubling identities write each value as 3a²+2ab+4b² with coprime a,b. If a is odd, (2b,a) is a primitive pair. If a is even, write a=2s. Then v/4 is the norm of the primitive pair (b,s). Every representation of an even norm has both coordinates even, and doubling gives a bijection from representations of v/4 onto those of v.

## Verification

`lucasFibonacciSum_prime_iff_four_representations` uses the upstream sequence directly. `primitive_eleven_form_count`, `prime_iff_four_eleven_representations` and `odd_hosoya_representation_counts` state the divisor count, the general prime criterion and the two diagonal counts. The original cube exclusions remain in the shared module. [Notebook replay](../../README.md#replay)

The pinned source and three notebook modules compiled from fresh output with Lean 4.33.1. Independent kernel replay passed for each notebook module. All 19 named axiom reports used only `propext`, `Classical.choice` and `Quot.sound`. Searches of open and closed DeepMind and OMA issues and PRs found the original question and its statement PR. No matching formalization appeared in those searches or in the 4,295 LTS solved records checked. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/8156) · [OMA](https://github.com/GuillaumeBAUD-coder/open-math-agents) · [LTS](https://lefttosolve.com/api/solved)
