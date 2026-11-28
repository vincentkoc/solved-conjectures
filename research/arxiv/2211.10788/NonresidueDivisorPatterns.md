# Prime divisors that never occur as upper Hosoya values

Write Uₙ = Fₙ + Lₙ₊₁. On a positive-step index progression r + dt, **infinitely many primes that are nonsquares modulo 11 divide composite terms if and only if the progression contains an even index**. The primes supplied by the theorem are 3 modulo 4 and never equal any Uₙ. In the other direction, every odd prime nonsquare modulo 11 is absent as a divisor at every odd index. For example, U₁₂ = 665 has two such divisors, 7 and 19. [Lean proof](LucasFibonacciNonresidueProgressions.lean)

The result also specifies which **finite patterns** of these divisors can occur. Let nᵢ(t) = rᵢ + dᵢt, with each dᵢ positive. For every cutoff B the following conditions are equivalent.

1. Some parameter t makes all the nᵢ(t) even.
2. There is a parameter progression s + ej with e > 0 and distinct primes pᵢ > B, all 3 modulo 4 and nonsquare modulo 11, and positive odd integers vᵢ such that pᵢ has **exactly exponent vᵢ** in U at index nᵢ(s + ej) for every j ≥ 0.

The same index form can appear more than once. Thus one term can be assigned arbitrarily many distinct primes of this kind in its squarefree part, with the same exponents throughout a whole progression. Indices t and t + 1 cannot support them simultaneously. Indices t and t + 2 can. One instance is U₁₀ = 254 = 2·127 and U₁₂ = 665 = 5·7·19.

For pairwise distinct affine forms with a common even parameter, every nonempty subset product is nonsquare throughout a single progression. The steps may differ. For any two distinct coefficient pairs, all the gcds of the two upper values divide a fixed positive integer. Choose the assigned primes above the bounds for every pair. Each assigned prime then occurs to an odd exponent in its own term and is absent from all the others. [Affine gcd proof](LucasFibonacciAffineGCD.lean)

### Why the gcds are bounded and periodic

Write ω² = ω+1 in the integer quadratic algebra. The identity ωⁿ = Fₙ(ω−4) + Uₙ follows from the Fibonacci recurrence. For a common divisor q of U at indices r+dt and s+ft with d<f, reduce this identity modulo q at both indices. The element ω is a unit with inverse ω−1, and the Fibonacci coefficients at the two hits are units modulo q. Raising the two identities to powers f and d eliminates the term containing t. It follows that q divides the coefficient of ω in

```text
(ω−1)^(fr) · ω^(ds) · (ω−4)^(f−d).
```

This integer coefficient is nonzero. Modulo 11 the algebra has evaluations at 4 and −3. The first sends the displayed element to zero and the second sends it to a unit. A scalar would have the same image under both. For equal steps, the earlier common-divisor identity bounds the gcd by the Fibonacci number at the difference of the offsets. [Common-divisor identity](LucasFibonacciSmoothBlocks.lean)

The gcd itself is periodic from t = 0 for every pair of distinct forms. Modulo their fixed bound, ω is a unit in a finite ring, so both upper sequences repeat. The residues modulo that bound determine the gcd. For identical positive-step forms the gcd is the strictly increasing upper value itself. For identical constant forms it is constant. In particular, the upper values at indices kt and (k+1)t are coprime for every k and t, since their coefficient bound is 1.

### The parity obstruction

The recurrence gives Uₙ ≡ 4ⁿ modulo 11, so every upper value is a square modulo 11. Cassini’s identity at an odd prime p dividing Uₙ gives 11 ≡ (−1)ⁿ Uₙ₊₁² modulo p. If p is a nonsquare modulo 11, quadratic reciprocity first forces p ≡ 3 modulo 4. If n were odd, both 11 and −11 would be squares modulo p, making −1 a square as well. This proves necessity. [Earlier divisor exclusions](ExcludedPrimeDivisors.md)

### Producing fresh divisors

Extend the Fibonacci recurrence to negative indices and write Vₙ = Fₙ + Lₙ₋₁ for the lower diagonal. On any progression 2(r + dt) of even indices, choose a negative index in the same residue class modulo 2d. There U₋₂ₐ = −V₂ₐ. Put u = V₂ₐ > 0. Take M = max(B,u). The recurrence on consecutive Fibonacci residues is invertible modulo u·11·M!, so some nonnegative index of the progression has U ≡ −u modulo u·11·M!. Write U = uc. Then c ≡ −1 modulo 11·M!. Since −1 is a nonsquare modulo 11, at least one nonsquare prime factor of c has odd exponent. Every prime at most M divides M! and therefore cannot divide c. The chosen prime exceeds both B and u, so it has the same odd exponent in U.

For a finite family, first restrict to parameters of the same parity as a simultaneous even witness. After assigning a prime with exponent v, use periodicity modulo its (v+1)st power to keep the exponent exactly v on a subprogression. The next form still has a positive step and even indices. Choosing its prime above all those already used proves simultaneous divisibility with distinct primes.

### Scope and replay

The pinned DeepMind statement asks whether infinitely many primes **equal** some Uₙ. It remains open. Moree and Stevenhagen studied the density of primes dividing the full Lagarias sequence under GRH. The sequence here starts one index into theirs. The parity criterion above is unconditional and concerns divisors on prescribed index progressions. [Pinned declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Ching et al., p. 3](https://arxiv.org/pdf/2211.10788#page=3) · [Moree and Stevenhagen](https://arxiv.org/abs/math/9912253)

The six declarations in the [divisor-pattern proof](LucasFibonacciNonresidueProgressions.lean) include `nonresidue_divisor_patterns_iff`, `infinite_nonvalue_prime_divisors_iff` and `affine_upper_products_nonsquare`. The [gcd proof](LucasFibonacciAffineGCD.lean) exports `affine_upper_gcd_bound`, `affine_upper_gcd_periodic_iff` and `consecutive_multiple_upper_coprime`. Independent kernel replay checks both modules. Their axiom reports contain only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the formalization. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/8156) · [OMA search](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%222211.10788%22) · [LTS](https://lefttosolve.com/api/solved) · [Replay](../../README.md#replay)
