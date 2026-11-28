# Factorial collisions with prescribed prime gap lengths

For a prime $p$, call $\ell$ a **witnessed gap** if $j!\equiv(j+\ell)!\pmod p$ for some $1\le j<j+\ell<p$. Fix a finite set $S$ of prime gap lengths and write $H_p(S)$ for its witnessed members. The lower relative natural density of primes witnessing **every** length in $S$ is at least $\prod_{\ell\in S}1/\ell$. The upper relative natural density of primes witnessing **none** is at most $\prod_{\ell\in S}(1-1/\ell)$. For $S=\{2,3,5\}$ these bounds are $1/30$ and $4/15$, respectively. They count collisions between factorials in the exact interval of the pinned problem. [Unconditional declarations](Erdos478NaturalGapSieve.lean.in) · [Pinned Erdős 478](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean)

## How far to look for a collision

Take $S_K$ to be the primes through $K$. For $K\ge1$, the upper relative density of primes with $H_p(S_K)=\varnothing$ is at most $1/\log(K+1)$. More generally, fix nonnegative integers $K,D$ and $\eta>0$ satisfying
$$8^D<\eta^3\log(K+1).$$
For every sufficiently large $X$, fewer than $\eta\pi(X)$ primes $p\le X$ have $|H_p(S_K)|<D$. For example, choosing $\eta=2^{-D}$ and $K\ge\exp(64^D)$ suffices for $D\ge1$. The order of quantifiers matters. The gap cutoff is explicit in $D,\eta$. The proof gives no explicit starting value for $X$. [Cutoff proof](Erdos478GapCutoff.lean) · [Unconditional cutoff theorem](Erdos478NaturalGapSieve.lean.in)

The earlier density-one theorem concerns the total deficit $\delta_p=p-|\{j!\bmod p:1\le j<p\}|$ at each fixed threshold. This result specifies the lengths of the witnessed collisions and bounds their frequencies using a finite set $S$. Above a finite resultant cutoff, each length in $H_p(S)$ gives a different upper endpoint, hence $\delta_p\ge1+|H_p(S)|$. The extra class is zero. The upstream question asks whether the image size divided by $p$ tends to $1-1/e$ along all primes. That limit remains open. [Earlier density theorem](FactorialDeficitDensity.md) · [Endpoint and deficit bounds](Erdos478GapSieve.lean) · [Resultant argument](DisjointGapFamilies.md)

## The finite product bound

Let $B$ be a random subset of $S$ formed by selecting each $\ell$ independently with probability $1/\ell$. For any increasing family $E$ of subsets of $S$,
$$\liminf_{X\to\infty}\frac{\#\{p\le X:p\text{ prime},\,H_p(S)\in E\}}{\pi(X)}
  \ge \Pr(B\in E).$$
For decreasing $E$, the corresponding upper limit is at most $\Pr(B\in E)$. Thus the exceptional proportion for fewer than $D$ witnessed lengths has the explicit upper bound
$$\sum_{\substack{T\subseteq S\\ |T|<D}}
     \prod_{\ell\in T}\frac1\ell \prod_{\ell\in S\setminus T}\left(1-\frac1\ell\right).$$
Lean proves the one-sided bounds with an arbitrary positive error and an eventual quantifier over $X$. Independence belongs to the auxiliary set $B$. The actual events that individual gap polynomials have a root can be dependent. [Product weights and comparison](Erdos478GapSieve.lean) · [Prime proportions](Erdos478SieveProportions.lean)

For $\ell\in S$, let $r_\ell(p)$ count distinct roots of $G_\ell(x)=x(x-1)\cdots(x-\ell+1)-1$ over $\mathbf F_p$. For each $T\subseteq S$, the ordinary prime mean of $\prod_{\ell\in T}r_\ell(p)$ tends to one. To prove this, the root algebra for two monic irreducibles of coprime degrees embeds as a full-rank order in a number field. Its maps to $\mathbf F_p$ count pairs of roots. An integral primitive element supplies a single irreducible polynomial of product degree with that same root count away from finitely many primes. Iterating preserves coprimality for the next prime degree. The prime ideal theorem for the resulting field gives the mixed moment. [Product of root counts](Erdos478RootProduct.lean) · [Degree-one prime ideal input](Erdos478NaturalDensity.lean.in)

At each $p$, give a subset $T$ product weight with selection probabilities $r_\ell(p)/\ell$. Expanding its weight and applying the mixed moments gives exactly the limiting weight of $T$ under $B$. Every subset of positive weight lies inside $H_p(S)$ once $p$ exceeds all $\ell!$ for $\ell\in S$. This cutoff rules out an apparent repetition starting at $0!$. The logarithmic estimate uses $\log(K+1)\le\sum_{n\le K,\ n\ge1}1/n\le\prod_{\ell\in S_K}(1-1/\ell)^{-1}$. Weighting subsets by $2^{-|T|}$ and applying $(1-x/2)^3\le1-x$ for $0\le x\le1/2$ bounds the cube of the lower-tail probability by $8^D/\log(K+1)$. [Finite weights](Erdos478GapSieve.lean) · [Euler product and lower tail](Erdos478GapCutoff.lean)

Klurman and Munsch use irreducible factorial-gap polynomials to bound the mean deficit. In §3 they propose a product estimate based on a conjecture about intersections of splitting fields. Here coprime degrees give the mixed moments of root counts in root fields, which suffice for the one-sided comparisons above. Banks, Luca, Shparlinski and Stichtenoth give a quantitative growing deficit along a subsequence. The notebook’s earlier power-interval result also controls primes satisfying a progression condition. [Klurman and Munsch](https://www.numdam.org/item/10.5802/jtnb.974.pdf) · [Banks et al.](https://journals.tubitak.gov.tr/math/vol29/iss2/6/) · [Power intervals](DeficitPowerIntervals.md)

The 2026-11-28 overlap check found the DeepMind statement issue and statement PR, the open Left to Solve target, and OMA hits about a factorial sum and a divisor count. The repository’s earlier two-moment argument yields density one for fixed deficits. The finite product bounds here require all mixed moments. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5229) · [Left to Solve](https://lefttosolve.com/p/Erdos478.erdos_478) · [OMA factorial sum](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4056) · [OMA divisor count](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7450)

## Replay

The [notebook replay](../../README.md#replay) checks the four new native modules. The supplemental replay supplies the ordinary prime ideal theorem from the pinned Tau Ceti port, checks the source closure digest, builds in an empty directory and runs the independent kernel checker. From the pinned Formal Conjectures Lake environment, with `notebook` set to this repository’s `research` directory, run

```bash
lake env python3 "$notebook/erdos/478/replay-natural-density" --target gap-sieve
```

The clean replay checked 216 source modules and audited 25 named declarations from the new proof files. The seven unconditional declarations in `Erdos478.GapSieve` each report only `propext`, `Classical.choice` and `Quot.sound`. [Unconditional theorems](Erdos478NaturalGapSieve.lean.in) · [Replay script](replay-natural-density) · [Pinned prime ideal theorem](https://github.com/KitaKen1/simultaneous-primitive-roots/blob/bb3b4fff6bb0210a0f94fc535bf9adbf46ecc55a/lean/vendor/TauCeti/NumberTheory/ArithmeticDirichletSeries/Prime/PrimeIdealTheorem.lean)
