# Irreducible prefixes for both Jones chains from one seed

Fix a nonnegative integer s and a prime p > 2·16ˢ. Start **both** recurrences Tₙ₊₁ = XTₙ ± 1 at T₀ = p(X−1). Every Tₙ through index **4s²4ˢ**, inclusive, is irreducible over ℚ for either fixed sign. In particular, arbitrarily large prime coefficients give both signs any prescribed finite prefix. For p = 37 the bound reaches index 16; for p = 521 it reaches index 256. The theorem specifies a prefix and leaves its termination open. [Lean theorem](CunninghamSharedLinearPrefixes.lean)

The seed family was singled out by the complete cyclotomic calculation. There, a(X−1) with a ≥ 2 was exactly the family for which both signs avoid all cyclotomic factors at positive indices. The present bound excludes every rational factorization throughout the indicated prefix. Jones’s Corollary 1.6 gives infinite chains using separate seed families for the two signs. The pinned DeepMind questions ask for infinitely many natural prime seeds of each **exact** length under 2p±1. They remain open. [Cyclotomic classification](LinearCyclotomicFactors.md) · [Jones, §1 and §4](https://arxiv.org/pdf/1104.1579) · [Pinned integer predicates](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean)

## A polynomial test on every root

A primitive integral polynomial with prime leading coefficient has a factor with unit leading coefficient in any nontrivial integral factorization. Suppose an integral test polynomial G satisfies 0 < |G(z)| < 1 at every complex root z. For a nonconstant factor A with unit leading coefficient, the absolute resultant |Res(A,G)| is the product of these absolute values over the roots of A with multiplicity. It would be an integer strictly between zero and one. The Lean criterion uses a unit constant term to ensure primitivity. [Integral root test](CunninghamIntegralRootTests.lean)

The general large-prime irreducibility theory for f+pᵏg includes effective results of Bonciocat, Bugeaud, Cipu and Mignotte. For the Jones family the test polynomial below uses the recurrence to give one bound on both signs as the index varies. [Bonciocat et al., Theorem 1.1 and proof](https://irma.math.unistra.fr/~bugeaud/travaux/IrredCrit1.pdf)

## Balancing the roots inside and outside the unit circle

For n > 0, the constant term is ±1 and Tₙ(1) = ±n. Put R = |z| and B = |z−1|. At a root z, telescoping the recurrence gives pzⁿ(z−1)² = ±(1−zⁿ), hence

```text
p Rⁿ B² ≤ 1 + Rⁿ.
```

Take D = 4ˢ, K = sD and G(X) = Xᴷ(X−1). Its value at a root is nonzero. When R ≤ 1, suppose |G(z)| ≥ 1. Then B ≥ 1 and 2Rᴷ ≥ 1 since B ≤ 2. Raising the last inequality to 4s and using n ≤ 4sK gives D²Rⁿ ≥ 1. The root inequality now contradicts p > 2D².

When R > 1, the root inequality gives pB² ≤ 2, so DB < 1. Thus R ≤ 1+B < 1+1/D. Since (1+1/D)ᴰ ≤ exp(1) < 3, we have Rᴷ ≤ 4ˢ = D. This gives |G(z)| < 1 in the second region as well. [Root estimate](CunninghamBalancedRootEstimate.lean) · [Application to the two recurrences](CunninghamSharedLinearPrefixes.lean)

Lean 4.33.1 rebuilt and independently kernel-replayed five notebook modules. All 14 named axiom reports used only `propext`, `Classical.choice` and `Quot.sound`. Separate finite-field tests certified irreducibility over ℚ in all 72 sampled cases, for both signs through index 16 at p = 37 and index 20 at p = 521. Each test found a full-degree irreducible reduction; the largest field used had 277 elements. [Notebook replay](../../README.md#replay)
