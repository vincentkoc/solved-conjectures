# An exponential bound for factorial-residue shortfalls

For all sufficiently large integers $K$, and then all sufficiently large $X$ depending on $K$, the proportion of primes $p\le X$ with **at least $\lceil K/(4\log K)\rceil$ missing nonzero factorial residues** exceeds
$$
1-\exp\!\left(-\frac{K}{100\log K}\right).
$$
Each such prime has at least that many distinct repeated upper endpoints $j$. Each endpoint has a witness $1\le j-\ell<j<p$ with $(j-\ell)!\equiv j!\pmod p$, where $\ell$ is prime, $K<\ell\le2K$, and $\ell\equiv3,4\pmod7$. The constant $1/100$ can be replaced by any $A<1/96$. The previous estimate for this threshold and window bounded the exceptional fraction by $49\log K/K$. [Ordinary prime theorem](Erdos478NaturalExponentialTails.lean.in) · [Earlier variance bound](FrobeniusFactorialCollisions.md)

More generally, suppose $H(K)/K\to L>1$ and put $c=(L-1)/3$. For $b<c$ and $0<A<(c-b)^2/(2c)$, take $D=\lceil bK/\log K\rceil$ with the natural-number ceiling. For all sufficiently large $K$ followed by all sufficiently large $X$, more than a $1-\exp(-AK/\log K)$ fraction of primes through $X$ satisfy
$$
D\le T(K,p),\qquad |A_p|+D\le p-1.
$$
Here $T$ counts the distinct endpoints with prime lengths in $(K,H(K)]$ and the two classes above. The set $A_p=\{n!\bmod p:1\le n<p\}$ is exactly the image in the pinned conjecture. These inequalities give a one-sided bound for the deficit. The limit of $|A_p|/p$ along all primes remains open. [Window estimate](Erdos478ExponentialEndpointLaw.lean) · [DeepMind statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean)

## Why the mixed moments factor

Write $F_\ell(x)=x(x-1)\cdots(x-\ell+1)-1$ and let $R_\ell(p)$ count its roots modulo $p$. Select any finite family $S$ of primes $\ell>3$ in the two classes. For every $T\subseteq S$, the prime mean of
$$
\prod_{\ell\in S}R_\ell(p)\prod_{\ell\in T}R_\ell(p)
$$
is exactly $2^{|T|}$. Each square contributes two and each single count contributes one, even when the number of lengths is arbitrarily large. [Mixed-moment theorem](Erdos478JointGapMoments.lean)

Order the lengths by size and consider the largest one, $\ell$. The group acting on the smaller root sets embeds in a product of symmetric groups of orders $j!$ for $j<\ell$. Its order is prime to $\ell$. In the action on the $\ell$ new roots, the kernel fixing all smaller roots still contains an $\ell$-cycle. This normal subgroup acts doubly transitively. Indeed, in coordinates where the cycle is translation by one, if the kernel were affine then each conjugate of the cycle would be a fixed-point-free affine map, hence a translation. The ambient group would normalize the translations and would itself be affine. The binary Frobenius obstruction rules this out. The argument uses Burnside’s prime-degree theorem in Müller’s form. [Normal subgroup argument](Erdos478NormalPrimeRootAction.lean) · [Gap action](Erdos478RelativeGapPairs.lean) · [Müller](https://arxiv.org/abs/math/0310200)

Consequently one can move an ordered pair at length $\ell$ while fixing all earlier roots. Induction realizes every tuple identification preserving equality at each doubled length. This gives exactly $2^{|T|}$ orbits. Packing the tuples into roots of a separable polynomial over the rationals identifies the orbits with its rational irreducible factors. The degree-one prime ideal theorem then gives the mixed root-count mean. The argument uses joint moments of degree at most two in each length. The full joint distribution and Klurman and Munsch’s splitting-field intersection conjecture remain separate questions. [Joint orbits](Erdos478JointGapRootOrbits.lean) · [Equality patterns](Erdos478GapTuplePatterns.lean) · [Factor count](Erdos478RootOrbitFactorCount.lean) · [Tuple moments](Erdos478RationalWordOrbits.lean) · [Klurman–Munsch, §3](https://www.numdam.org/articles/10.5802/jtnb.974/)

## From moments to a prime-density bound

For $0\le z\le1$ and integers $n\ge0$, the quadratic $Q_z(n)=1-(1-z)n+(1-z)^2n(n-1)/2$ dominates $z^n$. The product of the $Q_z(R_\ell(p))$ has prime mean $((1+z^2)/2)^{|S|}$. Except at finitely many primes, the sum of the root counts equals the number of distinct positive repeated endpoints. Taking $z=e^{-\delta}$ and using $\cosh\delta\le e^{\delta^2/2}$ gives, for $m=|S|$ and $\delta\ge0$,
$$
\limsup_{X\to\infty}\frac{\#\{p\le X:p\text{ prime},\,T_S(p)<(1-\delta)m\}}{\pi(X)}
\le e^{-\delta^2m/2}.
$$
The Lean theorem gives the equivalent eventual inequality with any positive additive error. The two residue classes give $m\log K/K\to c$ in the proportional window. Choosing the relative shortfall to put the threshold at $bK/\log K$ gives the stated exponent. [Quadratic majorant](Erdos478QuadraticGapMajorant.lean) · [Finite-family bound](Erdos478GaussianGapTail.lean) · [Endpoint identification](Erdos478DistinctBandEndpoints.lean)

## Sources and replay

The notebook theorem `proportional_of_inputs` takes the degree-one prime ideal theorem and the prime-length counting asymptotic as hypotheses. The supplemental theorem `ordinary_proportional` discharges both using the pinned TauCeti prime ideal theorem, Wiener–Ikehara, and mathlib’s $L$-series results for primes in arithmetic progressions. From the pinned Formal Conjectures checkout, run `lake env python3 "$NOTEBOOK/research/erdos/478/replay-natural-density" --target exponential-tails`. The option `--archive PATH` reuses the pinned source tarball. [Replay script](replay-natural-density) · [Analytic adapter](Erdos478NaturalFrobeniusBands.lean.in) · [Pinned external source](https://github.com/KitaKen1/simultaneous-primitive-roots/tree/bb3b4fff6bb0210a0f94fc535bf9adbf46ecc55a/lean/vendor/TauCeti)

Klurman and Munsch study the prime mean of missing factorial residues and propose using joint splitting fields. Grebennikov, Sagdeev, Semchankau and Vasilevskii bound the number of represented residues from below. Abramov’s preprint concerns distinctness of $2!,\ldots,(p-1)!$. The estimate here localizes the collision witnesses and bounds the prime proportion with a prescribed shortfall. The DeepMind issue and statement PR and the open Left to Solve entry concern the full limit. The Open Math Agents declaration search returned no exact match. [Klurman–Munsch](https://doi.org/10.5802/jtnb.974) · [Grebennikov et al.](https://ems.press/content/serial-article-files/47109?nt=1) · [Abramov](https://arxiv.org/abs/2604.26429v8) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/4078) · [Left to Solve](https://www.lefttosolve.com/p/Erdos478.erdos_478) · [Open Math Agents search](https://github.com/lefttosolve2/open-math-agents/issues?q=Erdos478)

The clean Lean 4.33.1 build compiled 267 distinct modules, including 197 pinned external modules. Each object passed a separate kernel replay. The axiom audit covered 39 newly public declarations, all 70 public declarations in touched proof modules, and four analytic inputs. All reports used only `propext`, `Classical.choice`, and `Quot.sound`. Nine direct checks compared the pinned statement, witnesses, moments, prime fractions, and the dyadic specialization.
