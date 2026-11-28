# Prime divisors that never occur as upper Hosoya values

Write Uₙ = Fₙ + Lₙ₊₁. On a positive-step index progression r + dt, **infinitely many primes that are nonsquares modulo 11 divide composite terms if and only if the progression contains an even index**. The primes supplied by the theorem are 3 modulo 4 and never equal any Uₙ. In the other direction, every odd prime nonsquare modulo 11 is absent as a divisor at every odd index. For example, U₁₂ = 665 has two such divisors, 7 and 19. [Lean proof](LucasFibonacciNonresidueProgressions.lean)

The result also specifies which **finite patterns** of these divisors can occur. Let nᵢ(t) = rᵢ + dᵢt, with each dᵢ positive. For every cutoff B the following conditions are equivalent.

1. Some parameter t makes all the nᵢ(t) even.
2. There is a parameter progression s + ej with e > 0 and distinct primes pᵢ > B, all 3 modulo 4 and nonsquare modulo 11, such that pᵢ divides U at index nᵢ(s + ej) for every j ≥ 0.

The same index form can appear more than once. Thus one term can be assigned arbitrarily many distinct prime divisors of this kind, with the assignments persisting on a whole progression. Indices t and t + 1 cannot support them simultaneously. Indices t and t + 2 can. One instance is U₁₀ = 254 = 2·127 and U₁₂ = 665 = 5·7·19.

### The parity obstruction

The recurrence gives Uₙ ≡ 4ⁿ modulo 11, so every upper value is a square modulo 11. Cassini’s identity at an odd prime p dividing Uₙ gives 11 ≡ (−1)ⁿ Uₙ₊₁² modulo p. If p is a nonsquare modulo 11, quadratic reciprocity first forces p ≡ 3 modulo 4. If n were odd, both 11 and −11 would be squares modulo p, making −1 a square as well. This proves necessity. [Earlier divisor exclusions](ExcludedPrimeDivisors.md)

### Producing fresh divisors

Extend the Fibonacci recurrence to negative indices and write Vₙ = Fₙ + Lₙ₋₁ for the lower diagonal. On any progression 2(r + dt) of even indices, choose a negative index in the same residue class modulo 2d. There U₋₂ₐ = −V₂ₐ. Put u = V₂ₐ > 0. The recurrence on consecutive Fibonacci residues is invertible modulo u·11·B!, so some nonnegative index of the progression has U ≡ −u modulo u·11·B!. Write U = uc. Then c ≡ −1 modulo 11·B!. Since −1 is a nonsquare modulo 11, c has a nonsquare prime factor. Every prime at most B divides B! and therefore cannot divide c.

For a finite family, first restrict to parameters of the same parity as a simultaneous even witness. After assigning a prime to one index form, pass to a subprogression on which its divisibility persists. The next form still has a positive step and even indices. Choosing its prime above all those already used proves simultaneous divisibility with distinct primes.

### Scope and replay

The pinned DeepMind statement asks whether infinitely many primes **equal** some Uₙ. It remains open. Moree and Stevenhagen studied the density of primes dividing the full Lagarias sequence under GRH. The sequence here starts one index into theirs. The parity criterion above is unconditional and concerns divisors on prescribed index progressions. [Pinned declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Ching et al., p. 3](https://arxiv.org/pdf/2211.10788#page=3) · [Moree and Stevenhagen](https://arxiv.org/abs/math/9912253)

The four declarations in `Arxiv.«2211.10788»` are `upper_square_mod_eleven`, `nonresidue_prime_index`, `nonresidue_divisor_patterns_iff` and `infinite_nonvalue_prime_divisors_iff`. Their axiom reports contain only `propext`, `Classical.choice` and `Quot.sound`. The first uses only `propext` and `Quot.sound`. Live DeepMind and OMA issue and PR searches and the LTS solved records identified the canonical statement and no matching formalized divisor-pattern criterion. Codex assisted with the formalization. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/8156) · [OMA search](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues?q=%222211.10788%22) · [LTS](https://lefttosolve.com/api/solved) · [Replay](../../README.md#replay)
