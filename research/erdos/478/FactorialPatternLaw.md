# Exact densities for prescribed factorial collisions

For a prime $p$, write $A_p=\{j!\bmod p:1\le j<p\}$. Let $C_k(p)$ count indices $k+1\le j<p$ satisfying $(j-k)!\equiv j!\pmod p$. Thus the two indices in every counted pair belong to the interval used by Erdős 478. Call a gap $k$ saturated when $C_k(p)=k$. For each fixed $k\ge2$, one has $C_k(p)\le k$ for all sufficiently large primes. [Positive endpoints](Erdos478FactorialEndpointCounts.lean) · [Pinned conjecture](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean)

Fix a positive modulus $m$ and finite sets $S,T$ of integers at least two. For a finite set $V$ let $L(m,V)$ be the splitting field over $\mathbb Q$ of $\Phi_m$ and the polynomials $G_k(x)=x(x-1)\cdots(x-k+1)-1$ for $k\in V$. Consider the primes satisfying all four conditions.

- $m\mid p-1$.
- $C_k(p)=k$ for every $k\in S$.
- $C_k(p)<k$ for every $k\in T$.
- $|A_p|+\sum_{k\in S}k\le p-1$.

That density is exactly
$$\sum_{U\subseteq T}\frac{(-1)^{|U|}}{[L(m,S\cup U):\mathbb Q]}.$$
In particular, with $T=\varnothing$ the density is $1/[L(m,S):\mathbb Q]$, at least $1/(\varphi(m)\prod_{k\in S} k!)$. For $m=1$ and $S=\{2,3\}$, a set of primes of density at least $1/12$ has exactly two pairs at distance two, exactly three at distance three, and at least five missing nonzero residue classes. The formula allows intersecting fields and overlapping sets $S,T$. If the sets overlap, the event is empty. The theorem controls finitely many specified collision counts. The conjecture about the limit of $|A_p|/p$ remains open. [Ordinary density](Erdos478NaturalPatternLaw.lean.in) · [Field-degree bound](Erdos478GapSplittingDegrees.lean)

## Proof

Away from finitely many primes, the roots of $G_k$ in $\mathbf F_p$ are in bijection with the upper endpoints of the pairs. Primes exceeding $k!$ rule out the endpoint $j=k$, which would start the pair at $0!$. Saturation then means that all $k$ roots occur. The distinct irreducible factors in the test polynomial ensure separability over $\mathbb Q$ even when some polynomial is listed twice. The cyclotomic factor supplies the progression. The earlier disjoint-root bound on $|A_p|$ adds the saturated counts. [Endpoint bijection](Erdos478FactorialEndpointCounts.lean) · [Splitting test](Erdos478GapSplittingTest.lean) · [Disjoint roots and the deficit](Erdos478DisjointGapFamilies.lean)

For a monic separable integral polynomial of positive degree, a tagged ordering of its roots generates its splitting field. An automorphism fixing the tag fixes each root and hence the whole field. The tag's minimal polynomial has degree equal to the field degree. Outside the primes dividing two resultants its root count equals that degree times the complete-splitting indicator. The prime ideal theorem gives this irreducible polynomial mean root count one. Finite inclusion–exclusion now gives the displayed formula. The totient bound uses the degree of the cyclotomic field and the permutation action on each gap's roots. [Primitive tag](Erdos478SplittingFieldFactor.lean) · [Root count](Erdos478SplittingFactorCount.lean) · [Inclusion–exclusion](Erdos478GapPatternMeans.lean) · [Conversion to factorials](Erdos478FactorialPatternLaw.lean)

Complete-splitting density is the classical identity case of Chebotarev. The Lean derivation uses the degree-one prime ideal theorem through the notebook's checked Tau Ceti adapter. Klurman and Munsch use factorial-gap root fields to bound the average deficit and discuss splitting-field intersections. Banks, Luca, Shparlinski and Stichtenoth prove quantitative bounds along a subsequence. The notebook's earlier finite-gap sieve treats existence of a pair, and its fixed-deficit theorem gives density one when the gaps are left unspecified. The exact density above prescribes saturation and failure of saturation at named lengths. [Klurman and Munsch](https://www.numdam.org/articles/10.5802/jtnb.974/) · [Banks et al.](https://journals.tubitak.gov.tr/math/vol29/iss2/6/) · [Prime-gap sieve](PrimeGapSieve.md) · [Fixed deficits](FactorialDeficitDensity.md) · [Prime ideal theorem adapter](Erdos478NaturalDensity.lean.in)

The 2026-11-28 overlap check found the original DeepMind issue and statement PR, the open Left to Solve entry, and no matching joint-density proof in the Open Math Agents issue/PR search. This notebook contribution formalizes the finite-pattern law. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5229) · [Left to Solve](https://lefttosolve.com/p/Erdos478.erdos_478) · [Open Math Agents search](https://github.com/lefttosolve2/open-math-agents/issues?q=%22Erdos478.erdos_478%22)

## Replay

From the pinned Formal Conjectures Lake environment, with `notebook` set to this repository's `research` directory, run

```bash
lake env python3 "$notebook/erdos/478/replay-natural-density" --target patterns
```

The proof uses Lean 4.33.1, 28 notebook and adapter modules, and 197 modules in the pinned external source closure. The 15 axiom reports for the new proof files contain only `propext`, `Classical.choice` and `Quot.sound`. [Replay script](replay-natural-density) · [Pinned prime ideal theorem](https://github.com/KitaKen1/simultaneous-primitive-roots/blob/bb3b4fff6bb0210a0f94fc535bf9adbf46ecc55a/lean/vendor/TauCeti/NumberTheory/ArithmeticDirichletSeries/Prime/PrimeIdealTheorem.lean)
