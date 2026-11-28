# Prime divisors at prime indices on the upper Hosoya diagonal

Let `U(n) = 2Fₙ + Fₙ₊₂`. Infinitely many primes `q` each divide composite values `U(p)` at infinitely many prime indices `p`. The same conclusion holds for every `U(r+dp)` with `r ≥ 0` and `d > 0`. The two infinitudes are nested. For each fixed divisor, infinitely many prime parameters work. [Lean proof](LucasFibonacciPrimeIndices.lean)

The simultaneous theorem takes finitely many pairwise distinct pairs `(rᵢ,dᵢ)` with positive slopes and a bound `B`. There are distinct primes `qᵢ > B`, a positive modulus `L`, a residue `a` coprime to `L`, and a threshold `N`. For every `t > N` congruent to `a` modulo `L`, each `qᵢ` divides the corresponding composite value `U(rᵢ+dᵢt)`. Dirichlet’s theorem gives infinitely many prime parameters in this same class. The bound, the family and its slopes are arbitrary.

## Finding a divisor that can recur

Extend the Fibonacci recurrence to all integers, so that `U(−1) = 3`. Fix one form, write `w = U(r−d)`, and set `A = |w|`. The inequality `0 < A < U(r+d)` also covers negative starting indices. For example, at index `−(k+1)` the absolute value is `3Fₖ₊₁ − Fₖ`. The recurrence on consecutive pairs is invertible modulo `A·B!`, so its state at `r−d` has a positive return period `T`.

Choose a prime `ℓ > U(r+d)²` congruent to `−1` modulo both five and `T`, with `ℓ > 5`. Writing `u = U(r+dℓ)`, periodicity gives `u ≡ w mod A·B!`. Thus `u = AC`. Every prime factor of `C` exceeds `B`, since a prime `q ≤ B` dividing `C` would make `Aq` divide `w`. Also `u ≡ U(r+d) mod ℓ`. Indeed five is a square modulo `ℓ`, and Frobenius fixes each root of `X²−X−1` there.

If every prime factor `q` of `C` satisfied `q² ≡ 1 mod ℓ`, then `C² ≡ 1 mod ℓ` and `U(r+d)² ≡ A² mod ℓ`. These are distinct integers between zero and `ℓ−1`. This supplies a prime `q > B` dividing `u` for which `ℓ` is coprime to `q²−1`.

## A common prime progression

The notebook bounds the gcd of two upper values on distinct affine forms by a fixed positive multiple. Increase the cutoff beyond all those multiples and five, then choose the same `ℓ` for all the return periods. The divisors just constructed must be distinct, since a common prime would exceed the multiple bounding the corresponding gcd. [Affine gcd theorem](NonresidueDivisorPatterns.md)

For each selected `q`, the roots of `X²−X−1` are nonzero and distinct over the splitting field modulo `q`. Frobenius permutes them, so two applications fix each root and `q²−1` is a period of `U` modulo `q`. Take `L` to be the product of these periods. The class `ℓ mod L` preserves every divisibility and is coprime to `L`. Eventually each value exceeds its divisor, proving compositeness.

## Relation to the prime-value question

Ching, Flórez, Luca, Mukherjee and Saunders ask whether infinitely many primes **equal** an upper value. DeepMind’s declaration `infinitely_many_lucas_fibonacci_sum_primes` quantifies over precisely those primes. The theorem above concerns prime divisibility and supplies composite values on prime inputs. Infinitude of prime values remains open. [Paper, §5](https://arxiv.org/abs/2211.10788) · [Pinned Lean declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean)

Moree and Stevenhagen study the same recurrence with the initial pair `3,1`, one index earlier. Under GRH they determine the density of the primes dividing at least one term over all indices. The result for prime parameters is unconditional and restricts the parameters to primes. Song studies fifth powers among `Fₙ₊₅ + Fₙ = U(n+2)`. [Moree and Stevenhagen](https://arxiv.org/abs/math/9912253) · [Song](https://arxiv.org/abs/2611.19995)

Lean 4.33.1 compiled the pinned source and four notebook modules from fresh output. Four independent kernel replays passed. All fifteen axiom reports use only `propext`, `Classical.choice` and `Quot.sound`. The four declarations with axiom reports are `upper_quadratic_field_period`, `upper_split_prime_parameter`, `simultaneous_prime_parameter_divisors` and `infinite_recurring_divisors_at_prime_parameters`. [Notebook replay](../../README.md#replay)
