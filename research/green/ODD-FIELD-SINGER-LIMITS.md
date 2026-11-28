# Cubic Singer sums over odd finite fields

Let \(D\) be the cyclic labels of a cubic Singer hyperplane over an odd finite field of order \(Q\). Write \(v=Q^2+Q+1\) and \(S=D+D\). Along every sequence with \(Q\to\infty\), for every choice of centers \(c\), the fraction \(|S\cap(c-S)|/v\) tends to \(1/4\). The two reflected layers \(R\) in \(\mathbb Z/(2v)\) cover a fraction tending to \(7/8\) by ordinary two-sums. A full cyclic basis containing both layers has eventual normalized size above every constant smaller than \((3+\sqrt3)/(2\sqrt2)\). These statements allow the characteristic to stay fixed, the fields and hyperplanes to vary, and any finite number of even-characteristic terms in the sequence. [Overlap, coverage and repair bounds](Green33PrimeSingerCounts.lean)

Every center \(z\) has at least \(Q-80(\lfloor\sqrt Q\rfloor+1)-8\) ordered triple representations by \(D\). Outside one center it has at most \(Q+80(\lfloor\sqrt Q\rfloor+1)+10\). At \(Q\ge10000\) the unique global maximum is at three times the centroid, where the count is \(2Q+1\), \(2Q\), or \(2Q+2\) according as \(Q\bmod3\) is zero, one, or two. For the doubled cyclic set the finite bounds include \(32|(R+R)^c|\ge7Q^2\) at \(Q\ge10^6\). [Uniform lower estimate](Green33PrimeSingerTriples.lean) · [Exceptional pencil](Green33SingerExceptionalLabel.lean) · [Exact centroid peak](Green33PlanarMultipliers.lean)

## Character estimate

Let \(F\) be any finite field of odd characteristic and order \(Q\). If \(g\in F[X]\) has degree at most four and has a root of odd multiplicity in some finite extension, then its complete quadratic character sum satisfies
\[
 \left|\sum_{x\in F}\chi_F(g(x))\right|
 \le 80(\lfloor\sqrt Q\rfloor+1)+4.
\]
The estimate applies for every \(Q\), including extensions of a fixed small prime field. The classical Weil bound gives a sharper constant. The notebook gives a direct elementary Lean proof of the displayed estimate and uses it in the residual quadratic of a cubic pencil. [Finite-field estimate](Green33FiniteQuarticCharacter.lean) · [Cochrane and Pinner, *Using Stepanov's method for exponential sums involving rational functions*](https://www.sciencedirect.com/science/article/pii/S0022314X05000983)

## Where the characteristic enters

The auxiliary-polynomial argument tests points in a translated copy of the base field, where \(x^Q=x+c\). Its coefficient blocks have monomials with exponents \(jQ+i\). At an odd-multiplicity root, the two blocks have disjoint lowest exponents modulo \(Q\). The previously formalized prime-field proof used ordinary derivatives to enforce many zeros at every tested point. Over a fixed characteristic \(p\), repeated ordinary differentiation loses the order of a zero at multiplicity \(p\).

Write \(D_k\) for the Hasse derivative. The monomials \(wX^{jQ}\) have \(D_k=0\) for \(0<k<Q\), since the intermediate binomial coefficients of \(p^e\) are zero in the field. The Hasse product rule supplies polynomials \(J_{n,k}\) satisfying
\[
 f^kD_k(f^n g)=f^nJ_{n,k},\qquad \deg J_{n,k}\le\deg g+k\deg f.
\]
These are polynomial identities even at zeros of \(f\). Vanishing of \(D_k H(x)\) for \(0\le k<r\) gives multiplicity at least \(r\) by the Taylor expansion at \(x\). The resulting Stepanov count permits \(r\) as large as \(Q\). The old prime-field statements remain available under their original names and signatures. [Hasse coefficient and multiplicity argument](Green33FiniteQuarticCharacter.lean) · [Prime-field specializations](Green33PrimeQuarticCharacter.lean)

## Application to cubic pencils

For a monic cubic pencil over \(F\), let \(N\) count ordered affine pairs whose residual quadratic vanishes and has nonzero leading coefficient. For the lower estimate the cubic must have roots \(r,s,t\) in an odd-degree extension, with \(s\ne t\) and the pencil numerator nonzero at \(r\). Then \(Q\le N+80(\lfloor\sqrt Q\rfloor+1)+8\). On the upper side, either \(N\le Q+80(\lfloor\sqrt Q\rfloor+1)+4\) or the discriminant polynomial is a scalar times a square. Both statements include repeated parameters. [Cubic-pencil theorems](Green33SingerCubicFibers.lean)

The projective chart transfers each affine pair to an ordered triple. The scalar-square pencil singles out at most one cyclic center, which occurs at most once when summing over the fourth label. The Sidon property then converts the resulting fourth-order count to reflected overlap with the finite diagonal correction. Green 33 itself asks for ordinary cyclic two-sum bases of asymptotic coefficient \(\sqrt2\). At the exact pinned positive cyclic order a full basis retaining the paired layers eventually misses the tolerance \(\varepsilon=1/100\). The prime-field theorem for a freely chosen opposite layer uses an additional prime-field incidence bound. [Previous Singer application](PRIME-SINGER-EXCEPTION.md) · [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

As a finite check in characteristic three, exhaustive arithmetic in \(F=\mathbb F_3[T]/(T^9+T^4+2)\) gave four zeros of \(X^4+X+1\) and complete character sum \(-1\). Here \(Q=19683\) and the formal upper bound is \(11284\).

## Verification

Lean 4.33.1 elaborated the 25-module local import closure. Each final module passed independent kernel replay. All 170 declaration reports use only `propext`, `Classical.choice` and `Quot.sound`. Direct comparisons against the pinned Green 33 predicate checked both the finite ordinary-sumset exclusion and the eventual literal tolerance for full bases.
