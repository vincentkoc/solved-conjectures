# Bounded-degree factors along both entire Jones chains

Fix a degree bound D. There exists a threshold B(D) such that whenever a = p^{2r+1} ≥ B(D) with p prime, neither chain from the **same seed** a(X−1) has a proper nonconstant rational factor of degree at most D, at any index. Here a proper factor has a nonconstant cofactor. The threshold is uniform in p and r. At fixed D the quantifier over indices is unrestricted. The proof gives no single coefficient for which all degrees are excluded at once. [Uniform theorem](CunninghamBoundedDegreeChains.lean)

For every integer coefficient a ≥ 2 there is also an index bound. If a nonconstant rational polynomial of degree at most D divides the nth term of either chain, n > 0, then

```text
n ≤ C(D) · (1 + ⌊log₂(4a+1)⌋).
```

This includes a factor equal to the entire term. The constant is existential, obtained from fixed-degree Northcott finiteness. Given such a C(D), the uniform theorem takes B(D) = 2^{32(C(D)+1)}. [Factor index theorem](CunninghamBalancedFactorCutoff.lean) · [Earlier degree-one classification](RationalRootSpectrum.md)

## Proof

Write T₀ = a(X−1) and Tₙ₊₁ = XTₙ + ε for ε = ±1. At a root z the telescoping identity gives zⁿ(a(z−1)²+ε) = ε. For |z| < 1 this forces 1 ≤ (4a+1)|z|ⁿ. For |z| ≥ 1 the inequality max(1,|z|)ⁿ ≤ (4a+1)|z|ⁿ holds directly. Gauss's lemma lifts a rational divisor to an integral divisor f of the same degree. For n > 0 the constant coefficient of the iterate is a unit, hence so is f(0). Multiplying the root inequalities with multiplicities gives M(f)ⁿ ≤ (4a+1)^{deg f}, where M is Mahler measure. [Root product inequality and Northcott argument](CunninghamFactorMeasureBounds.lean)

Every nonconstant integral divisor has M(f) > 1. Equality would give a cyclotomic divisor by Kronecker's theorem, and the common seed a(X−1) excludes all such divisors at positive indices. Northcott finiteness for degree at most D and measure at most two gives a single K(D) such that 2 ≤ M(f)^{K(D)} whenever M(f) > 1 in that degree range. Taking powers in the measure estimate gives the stated bound with C(D) = DK(D). [Cyclotomic classification](LinearCyclotomicFactors.md) · [Mathlib’s Northcott and Kronecker theorems](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/MahlerMeasure.html)

For odd prime-power coefficients take s = ⌊(log₂ a)/8⌋. Above B(D), the shared irreducible prefix through 4s²4ˢ contains every index allowed by the bound. Beyond it there are no nonconstant factors of degree at most D. Within it each iterate is irreducible over the rationals. [Shared odd-prime-power prefix](FixedPrimePowerPrefixes.md)

## Relation to the sources

Jones proves the existence of infinite polynomial chains for each kind. The theorem here fixes the linear seed family, uses the same coefficient for both signs and bounds the degrees of possible proper factors. The logarithmic cutoff is a special case of the low-degree factor phenomenon studied by Lenstra for lacunary polynomials. Indeed (X−1)Tₙ = Xⁿ(a(X−1)²+ε)−ε. Sawin, Shusterman and Stoll study irreducibility of the nonreciprocal part of large-gap polynomials under hypotheses on the coefficient polynomials. The two pinned DeepMind predicates instead require natural prime values under 2p ± 1 and exact termination. Both infinitude conjectures remain open. [Jones](https://arxiv.org/abs/1104.1579) · [Lenstra](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1999a/art.pdf) · [Sawin, Shusterman and Stoll](https://arxiv.org/abs/1803.10811) · [Canonical declarations](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean)

Independent finite-field calculations certified the absence of factors of degrees one through three for all 280 terms with a in {17,125,128,243,343,1331,2048}, both signs and 4 ≤ n ≤ 23. In each case a full-degree reduction modulo a prime at most 103 was coprime to X^{qʲ}−X for j = 1, 2, 3, where q is the reduction prime. Integer arithmetic also checked the prefix and cutoff inequalities for 13,000 choices of coefficient and gap constant. An independent Lean 4.33.1 kernel replay checked eleven modules. All 27 named axiom reports used only standard axioms. [Kernel replay instructions](../../README.md#replay)
