# How many factorial windows contain a repeat?

Fix a prime $p$ and a span $H$. A positive start $a$ is valid when $1\le a$ and $a+H<p$. Let $D(a)$ count distinct residues among $a!,(a+1)!,\ldots,(a+H)!$ modulo $p$. With the start uniform among the $N=p-1-H>0$ valid starts, the following limits hold along the primes.

| Span | Window statistic |
| --- | --- |
| $H^3=o(p)$ | The probability of any repeat tends to zero. |
| $H^2=o(p)$ | The mean of $D(a)/(H+1)$ tends to one. For every fixed $\varepsilon>0$, the probability of losing at least $\varepsilon(H+1)$ values tends to zero. |
| $H/\sqrt p\to c$ | For every positive integer $m$, the lower limit of the mean of $D(a)/(H+1)$ is at least $(m-c^2/6)/\binom{m+1}{2}$. Choosing $m>c^2/6$ gives a positive bound for every fixed $c$. |

These are statements about starting positions within each prime. A second limit averages over the primes themselves. Fix $H$ first and let $B_p(H)$ count valid starts with any repeat, taking zero for an empty set of starts. Then
$$
\lim_{X\to\infty}\frac1{\pi(X)}\sum_{p\le X}B_p(H)=\binom H2.
$$
For example, four consecutive factorials have three nonadjacent position pairs. Each pair contributes one starting position on average over the primes. [Growing spans](Erdos478WindowScales.lean) · [critical scale](Erdos478CriticalWindowImage.lean) · [ordinary prime mean](Erdos478NaturalWindowIncidence.lean.in)

## Counting colliding translates

Let $E(a)$ count unordered pairs of distinct positions with the same residue. Fix positions $r<s$ in the window. Cancelling $(a+r)!$ shows that a collision makes $a$ a root of the monic polynomial
$$
F_{s,k}(x)=\prod_{j=0}^{k-1}(x+s-j)-1,\qquad k=s-r .
$$
There are at most $k$ possible starts. Adjacent positive positions never collide before $p$. Summing the degrees gives the finite bound
$$
\sum_{a}E(a)+H\le\binom{H+2}{3}.
$$
Every lost value costs at least one pair. In particular there is a window with all $H+1$ values distinct whenever $H+1<p$ and $\binom{H+2}{3}<p-1$. A residue of multiplicity $v$ costs $\binom v2$ pairs. Summing $mv\le\binom{m+1}{2}+\binom v2$ over occupied residues gives $m(H+1)\le\binom{m+1}{2}D(a)+E(a)$. Normalizing yields the critical-scale coefficient above. [Pair incidence](Erdos478WindowPairIncidence.lean) · [degree sum](Erdos478WindowCollisionEnergy.lean) · [multiplicities](Erdos478WindowOccupancies.lean) · [finite image bounds](Erdos478WindowImageLoss.lean) · [normalizations](Erdos478NormalizedWindowEnergy.lean)

## Why the fixed-span mean is exact

For $k\ge2$, $F_{s,k}$ is irreducible over $\mathbb Q$ of degree $k$, so none of $0,-1,\ldots,-H$ is an integer root. A prime exceeding all their absolute evaluations excludes every invalid residue at the boundary. Every modular root then gives one valid start, including for windows touching the first or last permitted index. The degree-one prime ideal theorem gives ordinary prime mean one for the number of roots of this irreducible polynomial. For fixed $H$, the earlier resultant bound excludes two distinct repeated pairs in a single window once $p>(H+2)^{H^2}$. Thus summing over the $\binom H2$ nonadjacent position pairs counts each exceptional start exactly once. This includes spans zero and one, whose exceptional counts vanish. [Boundary correspondence](Erdos478WindowBoundaryRoots.lean) · [pair isolation](Erdos478IsolatedWindowCounts.lean) · [mean identity](Erdos478MeanExceptionalWindows.lean) · [prime ideal input and attribution](Erdos478NaturalDensity.lean.in)

## Relation to Erdős 478

The pinned question asks for the limit of the full image size divided by $p$, with predicted value $1-e^{-1}$. The window image here uses the same factorial residue function on a subinterval of $[1,p-1]$. Its mean density is normalized by the window length. The global limit remains open. [Pinned DeepMind statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5229) · [Left to Solve](https://www.lefttosolve.com/p/Erdos478.erdos_478)

Klurman and Munsch use the factorial-gap polynomials and their rational irreducibility in estimates for the global mean deficit. They also prove image bounds uniform in a short interval's location. Garaev, Luca and Shparlinski study exponential sums on shifted factorial intervals. Grebennikov, Sagdeev, Semchankau and Vasilevskii give global and long-interval lower bounds. The earlier notebook result controls every start up to a logarithmic scale. Here the polynomial-scale estimates count exceptional starts, and the fixed-span mean counts them with ordinary prime weights. A search of the DeepMind, Left to Solve, OMA and personal-repository records found no matching declaration. [Klurman–Munsch](https://doi.org/10.5802/jtnb.974) · [Garaev–Luca–Shparlinski](https://arxiv.org/abs/math/0403422) · [Grebennikov et al.](https://doi.org/10.4171/RMI/1422) · [earlier spacing result](LocalFactorialSpacing.md) · [related OMA factorial-sum problem](https://github.com/lefttosolve2/open-math-agents/pull/4056)

## Verification

From the pinned Formal Conjectures checkout run `lake env python3 "$NOTEBOOK/research/erdos/478/replay-natural-density" --target window-incidence`. The supplemental target uses the existing pinned Tau Ceti port for the ordinary prime mean. The growing-span inequalities and limits build against the notebook and pinned mathlib alone.

Direct enumeration checked all 37,418 positive windows at primes through 101, including the finite degree sum and occupancy inequalities for four slopes. Across all 669 primes through 5,000, the total numbers of exceptional starts were 653, 1,964 and 3,935 at spans two, three and four, respectively.

Independent Lean 4.33.1 replay rebuilt and kernel-checked 278 modules, including all 197 pinned external modules. All eleven new proof objects matched the development build byte for byte. The axiom audit checked 42 new public declarations and four imported inputs. Their only axioms were `propext`, `Classical.choice` and `Quot.sound`. Nineteen direct comparisons checked the host statement and prime filter, the positive interval, the two averaging denominators, boundary cases and a critical-scale example.
