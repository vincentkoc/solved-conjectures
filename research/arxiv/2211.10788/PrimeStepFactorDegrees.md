# Factor degrees at prime Hosoya index steps

Let `U(r) = 2Fᵣ + Fᵣ₊₂` be the pinned upper diagonal. For a prime step ℓ, the integral index polynomial is `P(X) = H(r,ℓ;X,1)`. Its homogeneous form gives the actual value `U(r+ℓ(n+1))` at the pair `(Fₙ,Fₙ₊₁)`. The following test decides whether the affine polynomial is irreducible modulo **every** prime p. It also covers a zero leading coefficient. [Index forms](IndexForms.md) · [Lean classification](HosoyaFactorDegrees.lean) · [Pinned sequence and question](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean)

| Condition | When P is irreducible modulo p |
| --- | --- |
| p does not divide U(r) | Exactly when the projective root count is zero. |
| p divides U(r) and p = ℓ | Never. |
| p divides U(r), p = 5 and p ≠ ℓ | Exactly when ℓ = 2. |
| p divides U(r), p ≠ 5 and p ≠ ℓ | Exactly when the order of the signed residue below is ℓ−1. |

The signed residue is `−p mod ℓ` for `p ≡ 2,3 mod 5`, and `p mod ℓ` otherwise. The prime 11 divides no upper term. When p = ℓ the derivative vanishes, so the polynomial is never irreducible over the prime field, including in the first row. The previous root count uses one power in the quadratic algebra with `ω² = 1+ω`, together with separate formulas at 5 and 11. [All-prime root counts](ProjectiveRootCounts.md)

For `p ≠ 5,11`, suppose the form has a projective zero. Mark one such zero. Every irreducible affine factor away from that zero has degree equal to the order of the signed residue. If the marked zero is infinity, this covers **every** affine factor. If `p ≠ ℓ`, each factor occurs once and the affine degree is ℓ or ℓ−1 according as p does not divide or divides U(r). For example, at `(p,r,ℓ) = (2,1,5)` the zero at infinity leaves the irreducible quartic `X⁴+X+1`. At `(29,0,7)` there is no projective zero, and the septic is irreducible. Both examples are checked in Lean. [Factor degrees, separability and examples](HosoyaFactorDegrees.lean)

## From a factor to a root

The descent applies over any field in which 5 and 11 are nonzero. If a divisor of the affine polynomial has degree e coprime to the step d > 1, the homogeneous form has a projective zero over the base field. Let a and b be the roots of the Fibonacci quadratic, and put `A = (3+a)aʳ` and `B = (3+b)bʳ`. At each root x of a divisor g, the two-power identity gives `A(x+a)ᵈ = B(x+b)ᵈ`. Multiplying over the roots with multiplicity gives `Aᵉg(−a)ᵈ = Bᵉg(−b)ᵈ`. Choose c and s with `ec = 1+ds`. Reduce the polynomial `((3+X)Xʳ)ˢ g(−X)ᶜ` modulo `X²−X−1`. Its two coordinates give the required projective zero. At prime step and full degree, any proper positive factor degree is coprime to the step. [Descent](HosoyaFactorDegreeDescent.lean)

With a marked zero, divide the ratio of the two linear evaluations at a second zero by the corresponding ratio at the marked zero. The result is a nontrivial ℓth root of unity. Frobenius acts on this coordinate by raising it to p if it fixes a and b, and to −p if it exchanges them. The orbit length is the factor degree, giving the signed-order formula. Simplicity follows because the derivative is d times the index form of step d−1, and successive forms cannot vanish at the same point in the good characteristics. [Frobenius and derivative proofs](HosoyaFactorDegrees.lean)

The main declarations are `upperIndexPolynomial_irreducible_mod_prime_iff`, `upperIndexPolynomial_factor_degree` and `upperIndexForm_zero_of_coprime_factor` in `Arxiv.«2211.10788»`. These are unconditional results on the polynomials representing affine subsequences. Infinitude of primes equal to U(n) remains open. Open and closed DeepMind and OMA issues and pull requests and LTS solved records yielded no matching formalization. Codex assisted with the Lean proof. [Ching et al.](https://arxiv.org/abs/2211.10788) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/8155) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/8156) · [OMA search](https://github.com/lefttosolve2/open-math-agents/issues?q=Hosoya) · [LTS records](https://lefttosolve.com/api/solved) · [Notebook replay](../../README.md#replay)
