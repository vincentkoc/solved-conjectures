# Fixed divisors of the upper Hosoya index forms

Write `U(r) = 2Fᵣ + Fᵣ₊₂`. For offset `r ≥ 0` and step `d ≥ 1`, let H be the homogeneous form with coefficients `binom(d,i) U(r+i)`, and let `P(X) = H(X,1)`. The fixed divisor of a form is the nonnegative gcd of all its values at integer inputs. H and P have the same fixed divisor. The following table determines it prime by prime for every `e ≥ 1`. [Lean proof](LucasFibonacciFixedDivisors.lean) · [Definition and irreducibility of P](IndexForms.md)

| Prime | When pᵉ divides every value |
| --- | --- |
| p = 5 | `5ᵉ ∣ U(r)` and `5ᵉ ∣ d` |
| p ≡ 2 or 3 mod 5 | `pᵉ ∣ U(r)` and `(p+1)p^(e−1) ∣ d` |
| p ≡ 1 or 4 mod 5 | Never |

At `r = 3, d = 12` the fixed divisor is exactly 9 since `U(3) = 9`. The polynomial is irreducible over ℚ and its coefficients have gcd 1. More generally, for every `k ≥ 0` some offset and step give a primitive irreducible polynomial with every integer value divisible by `3^(k+2)`. Take `d = 4·3^(k+1)` and choose r using the unbounded 3-adic valuations of U. [Prime-power lifts](PrimePowerLifts.md) · [Coefficient content](IndexForms.md)

## Computing the fixed divisor

Work in the quadratic ring with `ω² = 1+ω`. Write `(x+yω)ᵈ = u+vω`. Then `H(x,y) = U(r)u + U(r+1)v`. The point (1,0) forces a fixed divisor to divide U(r). Consecutive upper values are coprime, so modulo such a divisor the condition becomes `v = 0` for every pair.

For a split prime different from 5, the two roots a and b of the quadratic are distinct. Taking `x = −a, y = 1` gives 0 at a and a nonzero power at b. A scalar has the same value at both roots. For an inert prime, the algebra over the residue field is the field of p² elements. Its multiplicative group is cyclic and the scalar subgroup has index p+1. Every dth power is scalar exactly when `p+1 ∣ d`. Quadratic reciprocity gives the residue classes in the table, with 2 checked directly.

If the imaginary coefficient of an integral element is divisible by `pˢ` for `s ≥ 1`, its pth power gains another factor of p. For odd p the element `1+pω` forces the converse exponent bound. If `d = pᵃl` with `p ∤ l`, its dth power has imaginary coefficient congruent to `p^(a+1)l` modulo `p^(a+2)`. At 2 only the first two powers need checking because 8 divides no upper value.

At 5 the fifth-power formula for the imaginary coefficient gives sufficiency. For necessity take `z = 2ω`. Modulo 5, `(z−1)² = 0`, so a scalar dth power forces `5 ∣ d`. Over the integers, `z⁵ = 1+5(19+32ω)`. Since 5 does not divide 32, the same lifting argument detects each further power.

## Why integer values of P suffice

In the quadratic algebra modulo a prime power, write `t = ωᵈ` and `L(u+vω) = U(r)u+U(r+1)v`. If P vanishes everywhere, its values at 0 and 1 give `L(t) = L(t²) = 0` since `ω² = 1+ω`. The quadratic equation of t and its invertible norm give `L(1) = 0`. It follows that t itself is a scalar unit.

For any pair (x,y) with y a unit, homogeneity gives `H(x,y) = yᵈP(x/y)`. If x+y is a unit, multiplication by ω replaces (x,y) with (y,x+y), and multiplies the form value by the scalar unit t. In the remaining case p divides both coordinates. Factoring out p and descending one exponent proves divisibility for every integer pair.

## Relation to prime values

At Fibonacci pairs the form gives `U(r+d(n+1))`. The classification detects every fixed prime-power obstruction on all integer inputs. Specialization to Fibonacci pairs can impose further divisibility. Whether infinitely many primes equal whole upper values remains the open DeepMind question. Schinzel studies maximal fixed divisors across primitive forms of a prescribed degree and number of variables. The criterion here concerns one specified family. [Ching et al., §5](https://arxiv.org/abs/2211.10788) · [Pinned declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Schinzel, On fixed divisors of forms in many variables, I](https://tidsskrift.dk/math/article/view/17104) · [Divisors on index progressions](ProgressionDivisors.md)

Lean 4.33.1 compiled the pinned source and four notebook modules from fresh output. Separate kernel replays passed for all four. All 15 named axiom reports use only `propext`, `Classical.choice` and `Quot.sound`. The four result declarations are `upperIndexForm_power`, `upperIndexForm_fixed_prime_power`, `upperIndexPolynomial_fixed_prime_power` and `upper_primitive_forms_unbounded_fixed_powers`. [Notebook replay](../../README.md#replay)
