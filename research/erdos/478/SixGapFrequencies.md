# Exact frequencies for six-step factorial collisions

For a prime $p$, let $C_p$ count the upper endpoints $j$ with $1\le j-6<j<p$ and $(j-6)!\equiv j!\pmod p$. The following limits use all primes through $X$ as the denominator.

| $C_p$ | Relative natural density |
| --- | ---: |
| 0 | $7/12$ |
| 2 | $3/8$ |
| 6 | $1/24$ |
| Any other fixed count | $0$ |

There are exactly two primes outside the first three rows. The sole upper endpoint is $11$ at $p=17$ and $718$ at $p=719$. At $719$ the polynomial also has the root $6$, whose lower endpoint would be zero. For example, at $347$ the six upper endpoints are $24,53,146,206,299,328$. [All-prime classification](Erdos478SexticEndpoints.lean) · [Ordinary prime frequencies](Erdos478NaturalSexticCounts.lean.in)

For every modulus $m\ge1$, the primes $p\equiv1\pmod m$ with all two, four and six upper endpoints at those respective gaps, and $|A_p|+12\le p-1$, have natural density at least $1/(384\varphi(m))$. Here $A_p=\{j!\bmod p:1\le j<p\}$ is the exact image in Erdős 478. The earlier bound was $1/(768\varphi(m))$. The proof charges the sixth gap its exact splitting degree of $24$ and retains the paired bounds $2$ and $8$ at the other gaps. More generally, any disjoint finite list of additional even gaps $2r$ contributes at most $\prod_r 2^r r!$ to the denominator. The host question about the limit of $|A_p|/p$ remains open. [Joint degree estimate](Erdos478SexticSaturation.lean) · [Earlier bound](EvenGapDensity.md) · [Pinned host statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean)

## Why the three counts suffice

Write $f(x)=x(x-1)\cdots(x-5)-1$. With $s=2x-5$ and $w=s^2$, the identity $64f(x)=g(w)$ gives
\[
g(w)=w^3-35w^2+259w-289.
\]
The product of its three roots is $17^2$. If $a$ and $b$ supply two distinct pairs of signed roots, the third pair is $\pm17/(ab)$. The cubic discriminant is $64^2\cdot1957$ with $1957=19\cdot103$. At the exceptional characteristics for this argument the proof counts the positive endpoints directly. [Coordinate identity](Erdos478SexticResolvent.lean) · [Finite-field root counts](Erdos478SexticCoordinateCounts.lean)

The cubic is irreducible modulo three. Its splitting field $K$ has degree six over $\mathbb Q$. For any of its roots $w$, the cubic field $k=\mathbb Q(w)$ has $N_{k/\mathbb Q}(w)=17^2$. A square root of $w$ in $k$ would give a root of the irreducible degree-six gap polynomial. A square root of $1957w$ in $k$ would make $1957^3\cdot17^2$ a rational square. Quadratic descent from $K=k(\sqrt{1957})$ now shows that $w$ remains nonsquare in $K$. Two of the three roots have independent square classes because their product is $17^2$ divided by the third. Their two square roots generate precisely the sextic splitting field, of degree $6\cdot2\cdot2=24$. The LMFDB lookup by the expanded gap polynomial identifies field `6.6.3829849.1` and records the Galois group $S_4$ in its degree-six action `6T7`. The degree calculation in Lean is independent of that database. [Quadratic descent](Erdos478QuadraticSquareClasses.lean) · [Cubic norm argument](Erdos478SexticSquareClasses.lean) · [Splitting field](Erdos478SexticSplittingDegree.lean) · [LMFDB polynomial lookup](https://www.lmfdb.org/NumberField/x%5E6-15%2Ax%5E5%2B85%2Ax%5E4-225%2Ax%5E3%2B274%2Ax%5E2-120%2Ax-1) · [LMFDB field record](https://www.lmfdb.org/NumberField/6.6.3829849.1)

The first root moment is one. Complete splitting has density $1/24$. With support $0,2,6$ up to two primes, these two means and total mass one determine all three frequencies. Klurman and Munsch give the classical Galois interpretation of root counts for factorial-gap polynomials. The Lean proof uses the notebook’s first-moment and complete-splitting theorems, then discharges the analytic input with the pinned Tau Ceti degree-one prime ideal theorem. [Moment calculation](Erdos478SexticCountFrequencies.lean) · [Klurman and Munsch, §§2–3](https://www.numdam.org/articles/10.5802/jtnb.974/) · [Prior general count law](ExactCollisionCounts.md) · [Pinned analytic source](https://github.com/KitaKen1/simultaneous-primitive-roots/tree/bb3b4fff6bb0210a0f94fc535bf9adbf46ecc55a/lean)

## Replay and scope

From the pinned Formal Conjectures Lake checkout, run `lake env python3 "$notebook/erdos/478/replay-natural-density" --target sextic`, with `notebook` set to this repository’s `research` directory. The target includes the endpoint law and the twelve-collision progression bound. The live DeepMind issue and PR introduce the host statement. Left to Solve lists it as open. The searches of those trackers and Open Math Agents found no matching formal six-gap law. [Replay](replay-natural-density) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [DeepMind statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5229) · [Left to Solve](https://lefttosolve.com/p/Erdos478.erdos_478) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents/issues?q=%22Erdos478%22)

The independent Lean 4.33.1 replay covered all 246 modules in this target’s closure, including 197 modules from the pinned external source. All 22 public theorems introduced here use only `propext`, `Classical.choice` and `Quot.sound`. A separate comparison imported the pinned Erdős 478 file and checked the endpoint interval, the three fractions, the splitting degree, the canonical image bound and the endpoint sets at 17, 347 and 719.
