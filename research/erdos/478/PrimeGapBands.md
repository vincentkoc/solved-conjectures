# Polynomially many factorial collisions from a band of prime gaps

Fix real $0<\alpha<1$ and $\varepsilon>0$. For **every sufficiently large integer** $K$, put $D=\lceil K^\alpha\rceil$. Then for every sufficiently large $X$, a proportion greater than $1-\alpha-\varepsilon$ of the rational primes $p\le X$ have at least $D$ **distinct upper endpoints** $j$ of collisions
$$
(j-\ell)!\equiv j!\pmod p,\qquad 1\le j-\ell<j<p,\qquad D<\ell\le K,\quad \ell\text{ prime}.
$$
At each such prime the canonical factorial image $A_p=\{j!\bmod p:1\le j<p\}$ satisfies $\lvert A_p\rvert+D\le p-1$. The lower bound counts distinct indices even when different pairs give the same factorial residue. [Unconditional frequency](Erdos478NaturalPowerBands.lean.in) · [Exact witness event](Erdos478PowerBandQuantiles.lean) · [Pinned Erdős 478](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean)

For example, with $\alpha=1/2$, more than $1/2-\varepsilon$ of the primes through $X$ have at least $\lceil\sqrt K\rceil$ repeated indices from prime gaps in $(\lceil\sqrt K\rceil,K]$. With $\alpha=1/4$, the proportion exceeds $3/4-\varepsilon$ at the threshold $\lceil K^{1/4}\rceil$. The starting value of $X$ may depend on $K$. The conjectured limit of $\lvert A_p\rvert/p$ is still open. [Real exponents and integral cutoffs](Erdos478RealBandQuantiles.lean)

## The finite estimate

Write $U_p(S)$ for the union of positive collision endpoints over a finite set $S$ of prime lengths. For integers $0<M\le K$, take $S=\{\ell\text{ prime}:M<\ell\le K\}$ and let $b_X$ be the proportion of primes $p\le X$ with $\lvert U_p(S)\rvert<D$. For every $\varepsilon>0$, eventually in $X$,
$$
b_X < \prod_{\ell\in S}(1-1/\ell)+ D/M + \varepsilon .
$$
A second finite estimate bounds $(1-D/M)b_X$ by the same product plus $\varepsilon$. The proof of this latter estimate allows any finite set of prime lengths at least $M$. [Finite estimates](Erdos478WeightedBandSieve.lean) · [Ordinary prime specialization](Erdos478NaturalPowerBands.lean.in)

For each length $\ell$, let $r_\ell(p)$ be the number of roots of the polynomial $G_\ell(x)=x(x-1)\cdots(x-\ell+1)-1$ over $\mathbb F_p$. For each fixed $S$, the positive endpoint sets are pairwise disjoint and their union has size $\sum_{\ell\in S}r_\ell(p)$ outside finitely many primes. Separability over $\mathbb Q$ of $G_\ell G_k$ for $\ell\ne k$ supplies a resultant cutoff. A shared endpoint beyond the cutoff would give the reduced product a repeated root. Removing all the endpoints from the interval still leaves a representative of every factorial residue, since the least index giving any particular residue cannot be in the union. [Disjoint endpoints and the factorial image](Erdos478DistinctBandEndpoints.lean)

Set $u_\ell(p)=r_\ell(p)/\ell$. Distinct prime degrees give mixed root moments of one. Expanding over subsets therefore gives
$$
\lim_{X\to\infty}\frac1{\pi(X)}\sum_{p\le X,\ p\ {\rm prime}}\prod_{\ell\in S}(1-u_\ell(p))
=\prod_{\ell\in S}(1-1/\ell).
$$
Every $u_\ell(p)$ belongs to $[0,1]$. On the shortfall event outside the finite cutoff, $\sum_{\ell\in S}u_\ell(p)\le D/M$, so the product on the left is at least $1-D/M$. This uses the total number of endpoints at each gap. The earlier sieve counted witnessed lengths and gave a different dependence on the gap cutoff. [Mixed moments](Erdos478RootProduct.lean) · [Earlier finite gap sieve](PrimeGapSieve.md) · [Klurman and Munsch on factorial-gap polynomials](https://www.numdam.org/articles/10.5802/jtnb.974/)

## Passing to the power scale

Take $M=CD$ with $C$ a fixed positive integer. Mertens' product theorem gives
$$
\prod_{CD<\ell\le K,\ \ell\ {\rm prime}}(1-1/\ell)\longrightarrow \alpha
$$
because $\log(C\lceil K^\alpha\rceil)/\log K\to\alpha$. The finite estimate bounds the shortfall in the larger band $(D,K]$ by the smaller band's product plus $1/C$ and an arbitrary error. Choosing $C$ before $K$ gives the stated proportion. An integer-power version gives the same bound with gaps in $(t^a,t^b]$, threshold $t^a$ and limiting lower proportion $1-a/b$. [Band products](Erdos478MertensGapBands.lean) · [Cutoff transfer](Erdos478PowerBandQuantiles.lean) · [Rounding at real exponents](Erdos478RealBandQuantiles.lean)

The ordinary specialization imports the pinned Tau Ceti degree-one prime ideal theorem for the root moments and the pinned PNT+ Mertens product equivalence. The native proof states both inputs explicitly. [Prime ideal theorem](https://github.com/KitaKen1/simultaneous-primitive-roots/blob/bb3b4fff6bb0210a0f94fc535bf9adbf46ecc55a/lean/vendor/TauCeti/NumberTheory/ArithmeticDirichletSeries/Prime/PrimeIdealTheorem.lean) · [Mertens product theorem](https://github.com/KitaKen1/simultaneous-primitive-roots/blob/bb3b4fff6bb0210a0f94fc535bf9adbf46ecc55a/lean/vendor/PrimeNumberTheoremAnd/Erdos970/MertensClassical.lean) · [PNT+ project](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)

## Replay

From the pinned Formal Conjectures checkout run `lake env python3 "$NOTEBOOK/research/erdos/478/replay-natural-density" --target gap-bands`. The runner accepts a local pinned archive with `--archive FILE`. [Replay script](replay-natural-density) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5229) · [Left to Solve](https://www.lefttosolve.com/p/Erdos478.erdos_478)

A clean Lean 4.33.1 build and independent exact-name kernel replay covered all 238 modules in this target, including 199 pinned dependencies. All 16 new public theorems and the two analytic inputs depend only on `propext`, `Classical.choice` and `Quot.sound`. Seven direct checks compare the canonical conjecture, the positive endpoints, the prime gap interval, the distinct-index witness event, the prime-counting denominator and the quarter- and half-power specializations.
