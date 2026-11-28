# Irreducible forms for affine upper Hosoya indices

Let `U(n) = 2Fₙ + Fₙ₊₂`. For every offset `r ≥ 0` and every step `d ≥ 1`, define the homogeneous integral form

```text
H(r,d; x,y) = Σᵢ binom(d,i) U(r+i) x^(d−i) yⁱ,   0 ≤ i ≤ d.
```

It gives `U(r+d(n+1))` at `(x,y) = (Fₙ,Fₙ₊₁)` for every `n ≥ 0`, including the pair `(0,1)`. The initial value `U(r)` is `H(r,d; 1,0)`. Its polynomial `P(r,d; X) = H(r,d; X,1)` has degree d and is irreducible over ℚ. Two such polynomials are coprime over ℚ exactly when their pairs `(r,d)` differ. [Lean proof](LucasFibonacciIndexForms.lean)

The integer content is the gcd of the coefficients. For every prime p and positive k,

```text
pᵏ divides the content  ⇔  p = 5,  pᵏ divides U(r),  and  pᵏ divides d.
```

Thus the content is exactly the 5-part of `gcd(U(r),d)`. For instance, at `r=2, d=5` every coefficient is divisible by 5 and the leading coefficient is 5. A prime dividing every *value* of a polynomial can still be absent from its content. At `r=1, d=3` the form is `4x³+15x²y+27xy²+14y³`. Its coefficients have gcd 1, but modulo 2 it equals `xy(x+y)`, which vanishes at every pair of integers.

## Irreducibility at 11

The recurrence for the forms is `H(r,d+1) = x H(r,d) + y H(r+1,d)`, starting from `U(r)`. The Fibonacci addition formula gives the specialization on Fibonacci pairs. Modulo 11 the sequence is `U(r) ≡ 4ʳ`, so the translated polynomial `P(r,d; X−4)` reduces to `4ʳXᵈ`. Its leading coefficient is a unit modulo 11.

Modulo 121 the roots of the Fibonacci characteristic polynomial lift to 37 and 85. Matching the two initial terms gives `U(r) ≡ 100·37ʳ + 22·85ʳ`. Hence the translated constant is

```text
P(r,d; −4) ≡ 100·37ʳ·33ᵈ + 22·85ʳ·81ᵈ  (mod 121).
```

For `d ≥ 2` the first term vanishes and the second is divisible by 11 exactly once. Removing the integer content preserves these divisibility conditions since the leading coefficient is coprime to 11. Eisenstein’s criterion and Gauss’s lemma prove rational irreducibility, and reversing the translation preserves it. Degree one is immediate.

If two irreducible polynomials here share a nonconstant factor, they are rational multiples and have the same degree d. Their two highest coefficients are `U(r)` and `d U(r+1)`. Consecutive upper terms are coprime. Equality of the ratios `U(r+1)/U(r)` therefore gives equality of the positive denominators. Strict increase of U gives equality of the offsets.

## Why only powers of five occur in the content

Over a field of prime characteristic different from 5, the roots a and b of `X²−X−1` in its algebraic closure are distinct and nonzero. The polynomial is a linear combination of `(X+a)ᵈ` and `(X+b)ᵈ`, with coefficients `(3+a)aʳ/(a−b)` and `−(3+b)bʳ/(a−b)`. Evaluating at `−a` and `−b` shows that the combination could be the zero polynomial only if both a and b equal −3. This excludes every prime except 5. In any characteristic, a prime power dividing all coefficients divides both top coefficients. Coprimality of consecutive upper terms forces it to divide the step as well as the first upper value.

For the converse work in the quadratic algebra with `ω²=ω+1`. The form is the coefficient of ω in `(3+ω)ωʳ(x+yω)ᵈ`. The coefficient of ω in `(u+vω)⁵` equals `5v(u⁴+2u³v+4u²v²+3uv³+v⁴)`. Iteration supplies a factor `5ᵏ` in the ω coefficient of `(x+yω)ᵈ` whenever `5ᵏ ∣ d`. If `5ᵏ ∣ U(r)` also holds, multiplication by the initial factor preserves this divisibility.

## Relation to the prime-value question

The pinned DeepMind declaration asks whether infinitely many primes equal whole values of U. The forms above give an irreducible polynomial description for every affine index progression. Primality at infinitely many Fibonacci pairs remains open. The progression divisor criterion in the notebook treats primes dividing specialized terms. Flórez and Saunders study polynomial sequences of Fibonacci and Lucas type indexed by n, with irreducibility results for prime indices. Here r and d specify an affine index progression of a fixed integer sequence, and d can be composite. [Ching et al., §5](https://arxiv.org/abs/2211.10788) · [Pinned upper-diagonal declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean) · [Progression divisors](ProgressionDivisors.md) · [Flórez and Saunders](https://math.colgate.edu/~integers/w69/w69.pdf)

Lean 4.33.1 compiled the pinned source and the notebook module from fresh output. Independent kernel replay passed. The four axiom reports use only `propext`, `Classical.choice` and `Quot.sound`. The four result declarations are `upperIndexForm_fibonacci`, `upperIndexPolynomial_irreducible`, `upperIndexPolynomial_coprime_iff` and `upperIndexPolynomial_prime_power_content`. [Notebook replay](../../README.md#replay)
