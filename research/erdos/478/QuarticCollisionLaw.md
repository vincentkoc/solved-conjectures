# The first quartic factorial collision

For a prime $p$, count the upper endpoints of collisions of length $k$ by
$$
 C_k(p)=\#\{j:k+1\le j<p,\ (j-k)!\equiv j!\pmod p\}.
$$
The ordinary prime density of a **first** collision at distance four is $1/16$. The density of primes with no collision at any distance from one through four is $5/48$. The same two constants hold after requiring the factorial image to miss at least $h(p)$ residues, for one specified finite-search function $h(p)\to\infty$. [Unconditional limits and large examples](Erdos478NaturalQuarticLaw.lean.in) · [First-distance calculation](Erdos478ExactFourthAtom.lean)

## Joint distribution

The three counts $C_2,C_3,C_4$ are independent in their limiting distribution over rational primes. Each row gives its probability for every possible count. Multiply one entry from each row to obtain a joint probability. The Lean statement accepts any subset of the counts in each row, including the empty set. [Permutation counts](Erdos478PermutationCountLaw.lean) · [Endpoint law](Erdos478ExactFourthAtom.lean)

| Gap | 0 endpoints | 1 endpoint | 2 endpoints | 3 endpoints | 4 endpoints |
| --- | ---: | ---: | ---: | ---: | ---: |
| 2 | 1/2 | 0 | 1/2 | 0 | 0 |
| 3 | 1/3 | 1/2 | 0 | 1/6 | 0 |
| 4 | 5/8 | 0 | 1/4 | 0 | 1/8 |

Adjacent factorials on the host interval never collide modulo a prime. The event that $C_2=C_3=0$ and $C_4>0$ therefore gives $1/2\cdot1/3\cdot3/8=1/16$. Within that event, the pieces having two and four quartic endpoints have ordinary prime densities $1/24$ and $1/48$. At $p=47$ the first collision distance is four. The preceding notebook result certified a positive lower bound at this distance from that single prime. [Previous modular witness](ModularCollisionWitnesses.md)

## Three witnesses determine the joint action

Write $f_k(X)=X(X-1)\cdots(X-k+1)-1$. Away from the finitely many endpoint exceptions, congruence roots give exactly the counts in the table. The earlier endpoint correction accounts for the root $j=k$, which would use $0!$. At $p=23$, for example, $f_4$ has four roots and only three positive-index endpoints. In any common finite Galois splitting field, the same residue Frobenius lift realizes the root counts of all three polynomials at each of the following regular primes. [Modular certificates](Erdos478LowGapFrobeniusProfiles.lean) · [Endpoint correction](Erdos478ExactEndpointCorrection.lean)

| Prime | Roots of $f_2$ | Roots of $f_3$ | Roots of $f_4$ |
| ---: | ---: | ---: | ---: |
| 127 | 0 | 0 | 4 |
| 137 | 0 | 1 | 4 |
| 17 | 0 | 1 | 2 |

At 127 the action on the first two root sets is a transposition and a 3-cycle. At 137 the cubic action is a transposition. Both elements fix the quartic pointwise. Together they generate $S_2\times S_3$ on the first two sets. On the quartic roots, the involution $x\mapsto3-x$ pairs the four roots and commutes with every rational automorphism. Irreducibility gives transitivity, and the witness at 17 supplies a transposition. An element carrying a moved point of this transposition onto a fixed point interchanges the two pairs. These elements generate the full order-eight symmetry group of the pairing. The three actions jointly realize the full product. The quartic splitting field has degree 8, the compositum has degree 96, and every common finite normal splitting field over $\mathbb Q$ has degree divisible by 96. [Group criterion](Erdos478LowJointSurjection.lean) · [Root action](Erdos478QuarticRootActions.lean) · [Joint law](Erdos478QuarticJointAction.lean) · [Splitting degrees](Erdos478QuarticSplittingDegrees.lean)

## A single family with growing deficit

Let $\delta(p)=p-|\{j!\bmod p:1\le j<p\}|$ and let $\pi(X)$ count primes up to and including $X$. Compute the largest integer $q(X)\le X$ satisfying
$$
 (q(X)+1)\,\#\{p\le X:p\text{ prime},\,\delta(p)<q(X)\}\le\pi(X).
$$
Zero always qualifies. If $P_j$ is the prime with zero-based index $j$, put
$$
 H(p)=\max\{p,P_{\pi(p)^2}\},\qquad h(p)=\min_{p\le Y\le H(p)}q(Y).
$$
All searches at a given integer are finite. Fixed-threshold density one implies $q(X)\to\infty$, hence $h(p)\to\infty$. The proof supplies no elementary lower rate for either function. [Threshold construction](Erdos478RollingDeficitThreshold.lean) · [Fixed-threshold density one](FactorialDeficitDensity.md)

For any prime event $T$, let $F_X(T)$ be its fraction among the primes up to $X$. For $X\ge2$, simultaneously for every $T$,
$$
 0\le F_X(T)-F_X(T\cap\{\delta(p)\ge h(p)\})
 \le \frac{\lfloor\sqrt{\pi(X)}\rfloor}{\pi(X)}+\frac{1}{q(X)+1}.
$$
The error tends to zero. Indeed, except for at most $\lfloor\sqrt{\pi(X)}\rfloor$ early primes, the search interval for $h(p)$ contains $X$. On all other primes $p\le X$, failing the threshold implies $\delta(p)<q(X)$. This proves that a single pointwise growing deficit preserves every ordinary prime density. In particular, for all bounds $B,D$ there is a prime $p>B$ with first collision distance four and $\delta(p)\ge\max\{D,h(p)\}$. [Uniform error bound](Erdos478GrowingPrimeProfiles.lean) · [Unbounded prime witnesses](Erdos478NaturalQuarticLaw.lean.in)

## Scope, attribution and replay

The pinned question asks for the limit of the normalized image size along all primes, with proposed value $1-1/e$. The results here determine joint statistics at three fixed distances and give an unbounded absolute deficit on a family of a specified positive density. The normalized limit remains open. Banks, Luca, Shparlinski and Stichtenoth proved a growing deficit along a subsequence. Klurman and Munsch obtained quantitative mean bounds using factorial-gap polynomials and degree-one prime ideals. Short-gap obstructions also occur in the work on socialist primes. The exact joint formalization and finite threshold extend the earlier notebook results. Historical priority for the exact constants is unestablished. [Pinned Erdős 478](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean) · [Banks et al.](https://journals.tubitak.gov.tr/math/vol29/iss2/6/) · [Klurman and Munsch](https://www.numdam.org/articles/10.5802/jtnb.974/) · [Trudgian](https://www.kurims.kyoto-u.ac.jp/EMIS/journals/INTEGERS/papers/o63/o63.pdf)

The analytic adapter uses the checked degree-one prime ideal theorem from the pinned Tau Ceti port. Ordinary prime densities use the denominator $\pi(X)$. Live checks covered the DeepMind issue and statement entries, Left to Solve and Open Math Agents. [Prime ideal theorem sources](https://github.com/KitaKen1/simultaneous-primitive-roots/tree/bb3b4fff6bb0210a0f94fc535bf9adbf46ecc55a/lean/vendor/TauCeti) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/4078) · [Second statement entry](https://github.com/google-deepmind/formal-conjectures/pull/5229) · [Left to Solve](https://www.lefttosolve.com/p/Erdos478.erdos_478) · [Open Math Agents search](https://github.com/lefttosolve2/open-math-agents/issues?q=Erdos478)

From the pinned Formal Conjectures checkout, run `lake env python3 "$NOTEBOOK/research/erdos/478/replay-natural-density" --target quartic-law`. The optional `--archive` argument accepts the pinned port's source archive. [Reproduction script](replay-natural-density)

Independent kernel replay on Lean 4.33.1 covered 291 freshly compiled modules, including all 197 external modules from the pinned source closure. A separate axiom audit covered all 60 public declarations in the 12 added proof modules and the two analytic inputs. It found only `propext`, `Classical.choice` and `Quot.sound`. Twenty-five direct comparisons checked the host statement and denominator, the three witness primes, a boundary correction, the field degrees, the exact densities and the growing-deficit quantifiers.
