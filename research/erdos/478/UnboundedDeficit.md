# Unbounded gaps in the factorial value set

Let $A_p$ be the values of `n.factorial % p` for `n ∈ Ico 1 p`, exactly the finite image in the pinned problem. For every pair of natural numbers $D,N$, there is a prime $p>N$ for which 5 is a square modulo $p$ and $|A_p|+D<p$. Consequently there is a strictly increasing sequence of such primes on which $p-|A_p|$ tends to infinity. The proof gives no rate in terms of $p$. Erdős 478 asks whether $|A_p|/p$ tends to $1-e^{-1}$ along all primes. [Pinned statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean) · [Lean proof](Erdos478UnboundedDeficit.lean)

## Counting collisions

Write $G_k(X)=X(X-1)⋯(X-k+1)-1$, for $k≥2$. Each distinct root modulo $p$ gives a different upper endpoint $i$ at which the factorial repeats. Its least nonnegative representative satisfies $k≤i<p$, and $i!≡(i-k)!\pmod p$. If $i=k$, the earlier index 1 works because $0!=1!$. Every value has a least representative index, and none of these least indices is a repeated endpoint. Deleting all the endpoints therefore preserves the image, even when two endpoints give the same factorial value. This proves $|A_p|+\#\{G_k=0\}≤p-1$. Complete separable splitting yields $k+1$ missing residue classes, including zero.

## Producing the primes

For each prime degree $k$, reduction modulo $k$ gives $G_k=X^k-X-1$, whose derivative is $-1$. The integral resultant of the gap polynomial and its derivative is therefore nonzero. Its Bézout identity ensures separability at every prime larger than its absolute value.

The proof also formalizes a general splitting lemma. Any monic integral polynomial splits modulo arbitrarily large primes. In its rational splitting field, take an integral primitive generator. Schur’s prime-divisor argument supplies arbitrarily large primes where its minimal polynomial has a root. Away from the conductor exponent, the Kummer–Dedekind quotient equivalence lifts this evaluation to a map from the ring of integers to the prime field. Reducing the integral roots there gives a complete factorization. Applying the lemma to $G_k(X)(X^2-5)$ imposes the square condition at the same primes. Letting the prime degree grow proves both deficit assertions.

## Prior work and scope

Banks, Luca, Shparlinski and Stichtenoth established a quantitative lower bound for the number of missing residues along infinitely many primes. Klurman and Munsch use factorial-gap polynomials and establish a stronger average estimate in §2, Theorem 2.1. The contribution here is a Lean proof of the square-5 subsequence and of the splitting and counting lemmas it uses. The earlier notebook proof gave a fixed deficit of five. [Banks et al. (2005)](https://journals.tubitak.gov.tr/math/vol29/iss2/6/) · [Klurman and Munsch (2017)](https://doi.org/10.5802/jtnb.974) · [Earlier collision bound](MixedGaps.md)

The 2026-11-28 overlap check found the DeepMind statement issue and its formalization. Left to Solve listed the exact target as unsolved and unclaimed. The OMA factorial hits concerned a factorial sum and a divisor-counting problem. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5229) · [Left to Solve](https://lefttosolve.com/p/Erdos478.erdos_478) · [OMA factorial sum](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4056) · [OMA divisor count](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7450)

## Verification

The six public theorems in `Erdos478.FallingGap` are `card_add_gap_roots`, `card_add_of_splits`, `arbitrarily_large_splitting_prime`, `arbitrarily_large_split_gap`, `arbitrarily_large_deficit` and `exists_prime_subsequence`. A fresh Lean 4.33.1 build with warnings as errors and an independent `leanchecker` replay passed. Every declaration printed only `propext`, `Classical.choice` and `Quot.sound`. The notebook runner reproduces the audit. [Replay instructions](../../README.md#replay)
