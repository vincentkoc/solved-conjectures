# Prime densities for simultaneous even factorial collisions

Fix a modulus $m\ge1$ and a finite set $R$ of positive integers. For every $r\in R$, require exactly $2r$ distinct upper endpoints $j$ such that $1\le j-2r<j<p$ and $(j-2r)!\equiv j!\pmod p$. Also require $p\equiv1\pmod m$ and
\[
 |\{j!\bmod p:1\le j<p\}|+\sum_{r\in R}2r\le p-1.
\]
The relative natural density of these primes exists. With $P_R=\prod_{r\in R}2^r r!$, its value is at least $1/(\varphi(m)P_R)$. The denominator for the proportion of primes through $X$ is $\pi(X)$, including primes outside the progression. The empty set of gaps and modulus one are allowed. [Ordinary prime density](Erdos478NaturalPairedDensity.lean.in) · [Pinned Erdős 478](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean)

For $R=\{1,\ldots,n\}$ put $D=n(n+1)$. All $D$ prescribed collisions occur on a set of primes of density at least
\[
 \frac{\exp\!\left(-\tfrac D4\log(4D)\right)}{\varphi(m)}.
\]
Indeed $r!\le n^r$, so $P_R\le(2n)^{D/2}$, and $(2n)^2\le4D$. The earlier degree bound charged $(2r)!$ for the same gap. For $n=3$ the denominator at $m=1$ drops from $34560$ to $768$. At $p=1409$ the upper endpoints are $125,1285$ at gap two, $16,369,1043,1396$ at gap four, and $243,320,337,1077,1094,1171$ at gap six. The positive factorials occupy 920 residues. [Product estimate](Erdos478EvenGapDensityCost.lean) · [Progression bound](Erdos478EvenGapSaturation.lean) · [Earlier degree bound](Erdos478GapSplittingDegrees.lean)

## Why the Galois group preserves the pairs

Write $G_k(x)=x(x-1)\cdots(x-k+1)-1$. The involution $x\mapsto2r-1-x$ preserves $G_{2r}$. A fixed root in characteristic zero would be a zero of its derivative, contrary to separability. The $2r$ roots therefore form $r$ pairs. Every rational automorphism of the splitting field commutes with this reflection, because its formula has rational coefficients. Its action on the roots is faithful. The centralizer of the reflection has order $2^r r!$, counting a permutation of the pairs and one independent swap per pair. This gives the splitting-degree bound even when the Galois group is smaller. [Root reflection](Erdos478EvenGapReflection.lean) · [Centralizer calculation](Erdos478PairingCentralizer.lean) · [Faithful root action](Erdos478EvenGapGalois.lean)

The exact density is the reciprocal degree of the joint splitting field of the gap polynomials and the $m$-th cyclotomic polynomial. Using the upper bound on the degree of a compositum avoids assumptions on intersections of these fields. Banks, Luca, Shparlinski and Stichtenoth use gap-polynomial splitting to force missing factorial residues. Klurman and Munsch study the first root moment and discuss splitting-field intersections. The notebook previously used reflection to bound the height of an effective splitting certificate and proved the general factorial-pattern frequency. The new estimate uses reflection to bound the degree in that frequency formula. [Banks et al.](https://mospace.umsystem.edu/server/api/core/bitstreams/5b756a2f-14b6-4cd7-b23e-f57366effec4/content) · [Klurman and Munsch, §3](https://www.numdam.org/articles/10.5802/jtnb.974/) · [Effective reflection argument](Erdos478ChosenGapPairs.lean) · [Earlier density law](Erdos478NaturalPatternLaw.lean.in)

## Scope and replay

The finite gap set is fixed before taking the limit over primes. The bound quantifies the frequency of a prescribed pattern. The full conjecture asks for the limit of the normalized image size over all primes. The ordinary density here uses the checked degree-one prime ideal theorem from the pinned Tau Ceti port. [Source issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [Related upstream PR](https://github.com/google-deepmind/formal-conjectures/pull/5229) · [Left to Solve](https://www.lefttosolve.com/p/Erdos478.erdos_478) · [OMA issue and PR search](https://github.com/lefttosolve2/open-math-agents/issues?q=%22Erdos478%22) · [Pinned source port](https://github.com/KitaKen1/simultaneous-primitive-roots/tree/bb3b4fff6bb0210a0f94fc535bf9adbf46ecc55a/lean)

The independent replay checked 233 freshly compiled objects, comprising 36 notebook and adapter modules and 197 pinned external modules. All 13 public theorems in the changed Lean sources, including all 11 new declarations, passed the standard-axiom audit. The direct host comparison checked the positive interval, the empty product, the cost 768, and the actual endpoint sets and image size at $p=151$.

From the pinned Formal Conjectures Lake environment run the notebook's `research/erdos/478/replay-natural-density --target paired` under `lake env`. An existing pinned source archive can be supplied with `--archive`. [Runner](replay-natural-density)
