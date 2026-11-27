# Adding factorial collisions from different gap lengths

For a prime $p$, write $A_p=\{n!\bmod p:1\le n<p\}$. For every $m\ge1$ and every $L,N\ge0$, there is a prime $p>N$ with $p\equiv1\pmod m$ and
$$p-|A_p|\ \ge\ \binom{L+2}{2}.$$
At this prime the gap polynomials of lengths $2,\ldots,L+1$ split completely with distinct roots across the whole family. In particular, the lower bound counts simultaneous collisions with specified lengths. [Lean proof](Erdos478DisjointGapFamilies.lean)

## Counting the endpoints

Let $S$ be a finite set of integers at least two, $G_k(X)=X(X-1)\cdots(X-k+1)-1$, and $F=\prod_{k\in S}G_k$. At every prime $p>|\operatorname{Res}(F,F')|$ the following bound holds, where each root count includes multiplicity.
$$|A_p|+\sum_{k\in S}\#\{x\in\mathbf F_p:G_k(x)=0\}\ \le\ p-1.$$
The inequality also holds when some factors have no roots in the prime field. The earlier single-gap result counted roots for one prime gap length. [Single-gap proof](UnboundedDeficit.md)

A root with least representative $i$ gives $i!\equiv(i-k)!\pmod p$. If $i=k$, index 1 represents $0!$. Thus a root can never be the least index for its factorial residue. Distinct upper endpoints can all be discarded at once, even if their factorials coincide. This is the content of `card_add_gap_endpoints`. [Endpoint lemma](Erdos478UnboundedDeficit.lean)

To distinguish endpoints from different lengths, suppose $G_k=gh$ is a monic integral factorization of positive degrees. At $0,\ldots,k-1$ the product $gh$ equals $-1$, so $g+h$ vanishes at all $k$ points. Its degree is below $k$, forcing $g=-h$, contrary to monicity. Gauss's lemma gives irreducibility over $\mathbf Q$. Different degrees give distinct irreducibles. The product is therefore separable over $\mathbf Q$, and the integral Bézout identity for its resultant with its derivative preserves separability modulo every prime above the cutoff.

The earlier splitting-prime theorem applied to $Fg$ gives arbitrarily large primes where this entire family and any prescribed monic $g\in\mathbf Z[X]$ split. Taking $g=\Phi_m$ and $p>m$ supplies a primitive $m$th root, hence $m\mid p-1$. Summing the degrees for $2\le k\le L+1$ gives $\binom{L+2}{2}-1$. Zero supplies the remaining missing class. [Earlier splitting theorem](https://github.com/vincentkoc/solved-conjectures/pull/16)

## Scope and sources

The declarations `card_add_sum_gap_roots`, `arbitrarily_large_split_family` and `triangular_deficit_in_progression` are in `Erdos478.GapFamilies`. Their finite image is definitionally the one in the pinned `Erdos478.erdos_478`. That conjecture asks whether $|A_p|/p$ tends to $1-1/e$ along all primes. The theorem here gives a subsequence in each specified progression. A rate in terms of $p$, the density of the witnessing primes and the normalized limit remain outside its scope. [Pinned statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean)

Klurman and Munsch use translated factorial-gap polynomials and their irreducibility in §2 of *Distribution of factorials modulo p*. Their Theorem 2.1 gives a quantitative average result. Banks, Luca, Shparlinski and Stichtenoth had already proved a quantitative subsequence bound. This notebook contribution formalizes the additive endpoint count and simultaneous splitting in prescribed progressions. [Klurman and Munsch](https://www.numdam.org/item/10.5802/jtnb.974.pdf) · [Banks et al.](https://journals.tubitak.gov.tr/math/vol29/iss2/6/)

The overlap check on 2026-11-28 found the DeepMind statement issue and formalization, the open Left to Solve target, and OMA matches about a factorial sum and a divisor count. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5229) · [Left to Solve](https://lefttosolve.com/p/Erdos478.erdos_478) · [OMA factorial sum](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4056) · [OMA divisor count](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7450)

## Verification

Both modules were compiled into an empty directory under Lean 4.33.1 with warnings as errors. Independent `leanchecker` replay passed for both. The seven printed declarations in each module use only `propext`, `Classical.choice` and `Quot.sound`. [Replay instructions](../../README.md#replay)
