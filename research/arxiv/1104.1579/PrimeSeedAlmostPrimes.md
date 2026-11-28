# Prime seeds for rough almost-prime Cunningham prefixes

Fix a positive length $k$ and either recurrence $t_{i+1}=2t_i+1$ or $t_{i+1}=2t_i-1$. There is a prime $q$ such that, for every cutoff $B$, infinitely many **prime** seeds $p=t_0$ satisfy all three conditions.

- Every prime factor of each $t_i$ with $0\le i<k$ exceeds $B$.
- Each such term has at most $1152k+117$ prime factors counted with multiplicity.
- The term $t_k$ is composite and divisible by $q$.

The Lean theorem takes Bombieri–Vinogradov as an explicit input. This is a classical theorem. Earlier work in this notebook gave a smaller factor bound for an unrestricted integer seed. Jones’s conjecture requires every prefix term to be prime and remains open for $k\ge2$. [Prime-seed theorem](CunninghamPrimeSeedAlmostPrimes.lean) · [Integer-seed theorem](AlmostPrimePrefixes.md) · [Pinned Jones predicates](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean) · [Jones](https://arxiv.org/abs/1104.1579)

## Distribution input

The input is definitionally equal to the type of DeepMind’s `elliott_halberstam.variants.bombieri_vinogradov`. Only its range below level $1/2$ is needed. The proof uses level $1/4$. The pinned declaration records the solved statement with a proof placeholder. A separate Lean project supplies a proof for real endpoints and logarithmic exponents $A\ge1$. The notebook proves the adapter `of_real_prime_counting`. It identifies the inclusive counts at integer endpoints and takes the bound at $\max(1,A)$. The independent replay here covers the adapter and its downstream use. The external proof has its own dependency graph. [Pinned distribution statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Wikipedia/ElliottHalberstamConjecture.lean) · [External solution](https://github.com/kimihiro64/bombieri-vinogradov/blob/7a1748306e026825ed6a5555516cc2f28989b2ac/Solution.lean) · [Distribution estimates and adapter](CunninghamPrimeSieveDistribution.lean)

## Proof

Choose the seed’s classes at the small primes first. At a larger prime $\ell$, at most $k$ nonzero classes make a prefix term divisible by $\ell$. Their density among reduced classes has denominator $\ell-1$. A squarefree product $d$ incurs at most $k^{\omega(d)}$ residue-class errors. Cauchy–Schwarz bounds the weighted sum using Bombieri–Vinogradov and an Euler product of order at most $(\log x)^{k^2}$. Choosing a larger logarithmic exponent absorbs that loss. The constants are uniform in the initial modulus. [Weighted discrepancy and CRT](CunninghamPrimeSieveDistribution.lean)

Brun’s lower sieve groups primes into intervals $(w,w^2]$. Disjoint intervals ensure that each product of selected primes occurs once in a truncated intersection sum. Chebyshev’s lower bound then gives a surviving prime between $Z$ and $Z^{1152k+116}$ for arbitrarily large $Z$. Its first $k$ terms have size at most $Z^{1152k+117}$. All their prime divisors exceed $Z$, which gives the factor bound. To make $t_k$ composite, fix a smaller seed $v$ whose $k$th iterate is prime and prescribe $p\equiv v$ modulo that prime. The strict growth of both orbits from seeds at least two keeps it out of the prefix. [Block discrepancies](CunninghamPrimeSieveBlocks.lean) · [Prime lower sieve](CunninghamPrimeSieveCount.lean) · [Brun’s method, Ford’s notes](https://ford126.web.illinois.edu/sieve2023.pdf)

## Verification

Lean 4.33.1 independently kernel-replayed nine notebook modules. All 35 named axiom reports used only `propext`, `Classical.choice` and `Quot.sound`. A separate type check compared the input with DeepMind’s declaration and applied the adapter to the external challenge’s exact definition. Independent arithmetic checked 4,224 nonzero-residue tests, 3,328 rational CRT discrepancy bounds, and a prime seed for each sign and each length from one through ten at cutoff eleven. At length ten, the first-kind seed 58,484,579 has terminal divisor 5,119, and the second-kind seed 63,190,051 has terminal divisor 12,289.

Searches of DeepMind, Open Math Agents, and Left to Solve located the original statement and related reductions. The prime-seed almost-prime result belongs to the personal notebook. Codex assisted with the formalization. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/4755) · [OMA Cunningham work](https://github.com/lefttosolve2/open-math-agents/issues?q=Cunningham) · [LTS records](https://lefttosolve.com/api/solved) · [Notebook replay](../../README.md#replay)
