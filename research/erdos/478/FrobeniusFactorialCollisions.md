# Twice as many factorial-gap lengths in proportional intervals

Fix $L>1$ and an integer cutoff $H(K)$ with $H(K)/K\to L$. For a prime $p$, let $T(K,p)$ count the distinct integers $j$ for which some prime length $\ell$ satisfies
$$
K<\ell\le H(K),\quad \ell\equiv3,4\pmod7,\quad 1\le j-\ell<j<p,
\qquad (j-\ell)!\equiv j!\pmod p.
$$
Put $A_p=\{n!\bmod p:1\le n<p\}$ and $c=(L-1)/3$. For every $\eta>0$ and $A>c/\eta^2$, for all sufficiently large $K$ and then all sufficiently large $X$, the fraction of primes $p\le X$ satisfying both
$$
\left|T(K,p)\frac{\log K}{K}-c\right|<\eta,
\qquad |A_p|+T(K,p)\le p-1
$$
exceeds $1-A\log K/K$. In particular the fraction exceeds $1-\varepsilon$ for every fixed $\varepsilon>0$ in these iterated quantifiers. The earlier endpoint law used only the classes 11 and 17 modulo 21 and had center $(L-1)/6$. The classes 4 and 10 modulo 21 supply the additional prime lengths. [Ordinary prime law](Erdos478NaturalFrobeniusBands.lean.in) · [General band variance](Erdos478FrobeniusBandVariance.lean) · [Earlier two-class law](ProportionalFactorialCollisions.md)

For the window $(K,2K]$, more than a $1-49\log K/K$ fraction of primes have **at least $\lceil K/(4\log K)\rceil$ distinct repeated upper endpoints**, and at least that many missing nonzero factorial residues. In particular the fraction eventually exceeds 99%. Here $c=1/3$, and $c/(c-1/4)^2=48$. More generally any coefficient $b<c$ gives the analogous lower bound $\lceil bK/\log K\rceil$. The cutoff for $X$ may depend on $K$. DeepMind’s question asks whether $|A_p|/p\to1-1/e$ along all primes. [Integer deficit theorem](Erdos478NaturalFrobeniusBands.lean.in) · [Canonical statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean)

## Why both residue classes work

Let $G_\ell(X)=X(X-1)\cdots(X-\ell+1)-1$. For $\ell>3$ prime congruent to 3 or 4 modulo 7, its reduction modulo 2 has an irreducible cubic factor. In its rational splitting field the residue degree at every prime ideal over 2 is therefore divisible by 3. The older proof used the order of the whole Galois group and needed $3\nmid\ell-1$. [Binary cubic factor](Erdos478BinaryCubicGap.lean) · [Local degree divisibility](Erdos478CubicSplittingDegree.lean)

Lift squaring on the residue field to an element $\sigma$ of the decomposition group. The residue degree divides its order, so $\sigma^\ell\ne1$. If $\sigma$ fixed an integral root, its reduction would satisfy $x^2=x$, hence would be 0 or 1. At both values $G_\ell=-1$. Thus $\sigma$ fixes no root. In the affine group on $\mathbf F_\ell$, every fixed-point-free element is a translation and its $\ell$th power is the identity. Burnside’s prime-degree alternative, using Müller’s proof, now makes the root action doubly transitive. This argument also applies to lengths such as 31 and 67, both congruent to 1 modulo 3. [Frobenius lift](Erdos478ResidueFrobeniusAtTwo.lean) · [Derangement criterion](Erdos478PrimeDerangements.lean) · [Root action](Erdos478RootlessPrimeGaps.lean) · [Müller](https://arxiv.org/abs/math/0310200)

For any finite family of these lengths, double transitivity gives second root moment two. The mixed moment at distinct prime lengths is one. Away from finitely many primes the upper endpoints from different lengths are disjoint, so the limiting variance of their count equals the number of lengths. Each of the two reduced classes modulo seven contributes prime-count coefficient $1/6$. The scale $\log K/K$ and Chebyshev’s inequality then give the displayed bound. The prime ideal theorem supplies the root moments and the earlier Wiener–Ikehara adapter supplies the progression counts. Klurman and Munsch studied the average factorial-image deficit using these gap polynomials. [Pair moments](Erdos478CubicGapSecondMoment.lean) · [Endpoint variance](Erdos478LocalizedEndpointVariance.lean) · [Progression adapter](Erdos478NaturalProportionalCollisions.lean.in) · [Klurman and Munsch](https://www.numdam.org/articles/10.5802/jtnb.974/)

## Replay and scope

From the pinned Formal Conjectures Lake environment run `lake env python3 "$NOTEBOOK/research/erdos/478/replay-natural-density" --target frobenius-bands`. An existing source archive can be supplied with `--archive PATH`. The native theorem `rate_of_inputs` exposes the analytic hypotheses. The supplemental `ordinary_rate`, `ordinary_law`, `ordinary_deficit_rate` and `dyadic_quarter` discharge them. [Runner](replay-natural-density) · [Pinned Tau Ceti port](https://github.com/KitaKen1/simultaneous-primitive-roots/tree/bb3b4fff6bb0210a0f94fc535bf9adbf46ecc55a/lean/vendor/TauCeti) · [Frequency statements](Erdos478NaturalFrobeniusBands.lean.in)

The DeepMind issue and statement PRs concern the full limiting constant. Left to Solve marks it open. The Open Math Agents text matches concern different predicates. This contribution strengthens the earlier checked band law in the notebook. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5229) · [Earlier statement PR](https://github.com/google-deepmind/formal-conjectures/pull/4078) · [Left to Solve](https://www.lefttosolve.com/p/Erdos478.erdos_478) · [OMA factorial identity](https://github.com/lefttosolve2/open-math-agents/pull/7450) · [OMA Erdős 18](https://github.com/lefttosolve2/open-math-agents/pull/4056)

The clean Lean 4.33.1 build and independent kernel replay checked 255 modules, including all 197 pinned external modules. All 25 new declarations, all 47 public declarations in the touched proof modules, and four analytic inputs passed the axiom audit with only `propext`, `Classical.choice` and `Quot.sound`. Twelve direct checks cover the canonical limit, both factorial indices, the new congruence classes, ordinary prime fractions and the numerical deficit rate.
