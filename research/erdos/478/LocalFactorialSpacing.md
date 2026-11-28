# How many factorial residues can a short interval lose?

Let $p$ be prime, $1\le a$, and $a+H<p$. If
$$
p>(H+2)^{H^2},
$$
then among $a!,(a+1)!,\ldots,(a+H)!$ modulo $p$ at most one unordered pair is equal. The interval therefore gives either $H+1$ distinct residues or exactly $H$. The estimate holds for every starting point at once. More precisely, if two different pairs have respective index differences $k$ and $\ell$, then $p\le(H+2)^{k\ell}$. [Pair separation](Erdos478WindowRepetitions.lean) · [exact image count](Erdos478WindowImageCard.lean)

For any fixed $0<c\le\sqrt2$, take
$$
H(p)=\left\lfloor c\sqrt{\frac{\log p}{\log\log p}}\right\rfloor .
$$
This span tends to infinity and meets the cutoff for all sufficiently large $p$, including at $c=\sqrt2$. Along the prime filter, every moving interval inside $[1,p-1]$ of this span has image density tending to one relative to its length $H(p)+1$. Moreover, the primes for which **the minimum over all starting points is exactly $H(p)$** have relative natural density one. The denominator in this last density is the number of rational primes through $X$. [Logarithmic span](Erdos478LogarithmicWindowSpan.lean) · [moving intervals](Erdos478SharpLocalImage.lean) · [ordinary prime densities](Erdos478NaturalWindowSpacing.lean.in)

## Why two collisions force a small prime

If $i!$ and $j!$ agree in the interval, set $r=j-a$ and $k=j-i$. Cancelling the nonzero $i!$ makes $a$ a root modulo $p$ of
$$
F_{r,k}(X)=\prod_{h=0}^{k-1}(X+r-h)-1 .
$$
Each polynomial is monic and irreducible over the rationals. Translation preserves the irreducibility of the falling-factorial gap polynomial. Distinct parameter pairs give different polynomials. Degree distinguishes different lengths. When $r<s$, evaluation at $-s$ distinguishes the two shifts because all the factors for the first shift are nonzero and the second product vanishes. Thus two different pairs yield a nonzero integer resultant divisible by $p$. [Translated polynomials](Erdos478TranslatedGapPolynomials.lean) · [gap irreducibility](Erdos478DisjointGapFamilies.lean)

At a complex root of $F_{r,k}$ the product of the $k$ distances to the integers $h-r$ equals one. At least one of these distances is at most one. Since $k\le r\le H$, the centres for either collision lie in $[-H,0]$. Each difference between a root of one polynomial and a root of the other has absolute value at most $H+2$. The monic resultant is the product of exactly $k\ell$ such differences, giving the stated bound. [Root locations](Erdos478TranslatedGapRoots.lean) · [resultant estimate](Erdos478LocalCollisionResultant.lean)

## Why the minimum is attained

Under the cutoff, a window has just $H$ residues exactly when it contains a collision. Any two positive indices less than $p$ at distance at most $H$ fit in a valid window of span $H$. This remains true at both ends of the interval. Hence the minimum equals $H$ precisely when the prime has some collision of length at most $H$. [Equivalence for all admissible spans](Erdos478SharpLocalImage.lean)

For fixed $K$, the earlier first-collision law gives the limiting proportion of primes with no collision at distance at most $K$. That proportion tends to zero as $K$ grows. For any $H(p)\to\infty$ satisfying the cutoff eventually, first choose $K$ and then discard the finite initial segment where $H(p)<K$ or the cutoff fails. Every remaining prime where the minimum exceeds $H(p)$ belongs to the fixed-$K$ avoidance event. This proves density-one attainment for every such choice of $H$. The supplemental endpoint uses the pinned, checked degree-one prime ideal theorem from the Tau Ceti port. [Density transfer](Erdos478LocalWindowDensity.lean) · [earlier avoidance law](LeastFactorialCollision.md) · [analytic input](Erdos478NaturalDensity.lean.in) · [pinned Tau Ceti source](https://github.com/KitaKen1/simultaneous-primitive-roots/tree/bb3b4fff6bb0210a0f94fc535bf9adbf46ecc55a/lean/vendor/TauCeti)

## Scope and sources

Erdős 478 asks for the limit $1-1/e$ for the **whole** positive factorial image divided by $p$. The local limit above has denominator $H+1$ and concerns much shorter intervals. Klurman and Munsch use factorial-gap polynomials and prove an interval estimate at lengths $\gg p^{1/4}$. Grebennikov, Sagdeev, Semchankau and Vasilevskii give further bounds on large intervals. Xiyu Hu proves a global lower bound of order $p^{8/15}$. The notebook contribution here is the uniform at-most-one collision bound and its sharp minimum for a density-one set of primes. Historical priority for the spacing bound is unestablished. [Pinned Erdős 478](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean) · [Klurman–Munsch](https://doi.org/10.5802/jtnb.974) · [Grebennikov et al.](https://arxiv.org/abs/2204.01153) · [Hu](https://arxiv.org/abs/2608.01781)

The live DeepMind, Left to Solve and Open Math Agents searches covered both the host statement and local factorial collisions. The earlier notebook counts collision lengths across primes and parity products in the full image. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5229) · [Left to Solve](https://www.lefttosolve.com/p/Erdos478.erdos_478) · [OMA factorial-sum thread](https://github.com/lefttosolve2/open-math-agents/pull/4056) · [mixed parity products](MixedParityProducts.md)

## Verification

From the pinned Formal Conjectures checkout run `lake env python3 "$NOTEBOOK/research/erdos/478/replay-natural-density" --target window-spacing`.

An independent scan of all 1,953,147 positive windows of span three modulo 1,953,151 found exactly five with three distinct residues. Every other window had four. Checks modulo the Mersenne primes $2^{61}-1$ and $2^{521}-1$ also attained the one-pair bound at spans four and ten, using roots of the gap-two polynomial to locate collisions.

Independent Lean 4.33.1 replay covered 287 modules, including all 197 pinned external modules. All nine new modules produced byte-identical development and independent objects. The axiom audit checked 31 new public declarations and four imported inputs against `propext`, `Classical.choice` and `Quot.sound`. Nineteen direct comparisons covered the canonical interval, both density normalizations, boundary cases and the endpoint constant.
