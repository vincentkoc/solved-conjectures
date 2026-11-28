# Factorial quotients and visits to multiplicative cosets

Let $p$ be prime. Select any $M$ indices from $1,\dots,p-1$ and write them in increasing order. Let $W$ be the distance from the first to the last selected index, with $W=0$ for an empty selection. Let $D$ count the distinct quotients $j!/i!\pmod p$ between **successive selected indices**. Then
$$
8\max(M-1,0)^3\le 9D W^2.
$$
In particular, a selection of positive density in a long interval must realize a number of different successive quotients proportional to the interval length. This applies even when the selected factorials take many different values. [Finite inequality](Erdos478AdjacentFactorialQuotients.lean)

## Cosets and moving intervals

For a target set $S\subseteq\mathbb F_p^\times$, every successive quotient of two hits lies in $S/S$. If $M$ factorials hit $S$ in a closed interval of length $N$ in the positive index domain, then
$$
8\max(M-1,0)^3\le 9|S/S|(N-1)^2.
$$
For $S=gH$ a multiplicative coset, $S/S=H$. When $-1\in H$ and $g^2\notin H$, the stronger bound
$$
16\max(M-1,0)^3\le 9|H|(N-1)^2
$$
holds for every such interval. At $p=1009$, take $H=\langle354\rangle$ of order 144 and $g=11$. On the full positive interval the ordinary bound gives $M\le548$ and the reflected bound gives $M\le435$. Direct enumeration gives 140 hits. [Target sets and cosets](Erdos478CosetVisitBounds.lean) · [reflected coset bound](Erdos478WilsonCosetBounds.lean)

As $N\to\infty$, any target with $|S/S|=o(N)$ captures a vanishing fraction of the interval. Both the interval and the target may be chosen separately at each prime. This covers a coset of any subgroup of order $o(N)$. The earlier theorem for unstructured targets assumes $|S|=o(\sqrt N)$. [Moving-target limit](Erdos478CosetMassLimit.lean) · [earlier concentration bound](PrescribedFactorialResidues.md)

The range above $\sqrt N$ occurs at arbitrarily large primes. For each integer $t\ge2$ and every cutoff $L$, the proof gives a prime $p>\max(L,t^9)$ with $p\equiv1\bmod t^6$, and a subgroup of order $t^6$. Every coset contains at most $1+2t^8$ factorial positions in **every** interval of length $t^9$ inside $[1,p-1]$. Thus the subgroup order equals $N^{2/3}$, while the fraction of positions it captures is at most $N^{-1}+2N^{-1/9}$. Existence uses primes congruent to one and cyclicity of $\mathbb F_p^\times$. [Realized prime windows](Erdos478LargeCosetWindows.lean)

## Counting gaps

Fix a gap $k>0$ and quotient $u$. A pair of selected indices $i,j=i+k$ with $j!/i!=u$ makes $j$ a root of the monic degree-$k$ polynomial
$$
X(X-1)\cdots(X-k+1)-u.
$$
Its upper endpoints in the canonical interval are distinct field elements. Consequently at most $Dk$ selected pairs have gap $k$. The $R=\max(M-1,0)$ successive pairs have total gap length $W$. Charging the shortfall of each gap below an integer cutoff $h$ gives $6hR+Dh\le6W+Dh^3$. Rounding $\sqrt{2R/D}$ to a nearest integer and retaining the linear term gives the finite cubic inequality, including the small and empty cases. [Prescribed-quotient roots](Erdos478PrescribedQuotientRoots.lean) · [integer cutoff and rounding](Erdos478QuotientCubicPacking.lean)

Wilson reflection sends $(i,j)$ to $(p-1-j,p-1-i)$. The new quotient is $(-1)^{j-i}j!/i!$. In a coset with $-1\in H$ it still lies in $H$. Two values in $gH$ cannot have product $1$ or $-1$ when $g^2\notin H$. Hence the reflected starts and the selected starts are disjoint, and the reflected starts stay positive. Both sets consume roots of the same collection of degree-$k$ polynomials. This doubles the charge for every gap length. The argument also applies to any sign-stable quotient set when all selected products avoid the two Wilson values. [Wilson quotient identity and doubled capacities](Erdos478WilsonQuotientReflection.lean)

## Scope and attribution

Garaev, Luca and Shparlinski use prescribed gaps and polynomial root counts in Theorem 12 to bound the number of occurrences of one residue by $O(N^{2/3})$. Their Theorem 1 gives multiplicative-character estimates on intervals, with additional dependence on $p$. Here the finite estimates track the actual successive quotients and depend only on their number and the occupied span. The coset limit holds at every interval scale. [Garaev, Luca and Shparlinski](https://arxiv.org/pdf/math/0403422)

Erdős 478 asks whether the cardinality of the **whole** factorial image divided by $p$ tends to $1-e^{-1}$ along the primes. The results above bound occupation of structured subsets of the field and leave that density open. Hu obtains a global image lower bound $\gg p^{8/15}$. The live DeepMind, Left to Solve, OMA and notebook searches found the host statement and the earlier prescribed-residue bound. They found no matching declaration about successive quotients or reflected coset occupation. Historical priority for these particular inequalities is unestablished. [Pinned host](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [Left to Solve](https://www.lefttosolve.com/p/Erdos478.erdos_478) · [Hu](https://arxiv.org/abs/2608.01781) · [earlier notebook theorem](https://github.com/vincentkoc/solved-conjectures/pull/444)

## Verification

From the pinned Formal Conjectures checkout run `lake env python3 "$NOTEBOOK/scripts/replay-research" Erdos478LargeCosetWindows`.

Direct enumeration checked all 332,886 index subsets at primes through 19, including all 948 satisfying Wilson product separation. A second calculation checked 1,651,338 coset-window cases at odd primes through 71, including 531,892 separated cases with sign-stable subgroup. It checked the actual successive quotients and the applicable cubic bounds.

Independent Lean 4.33.1 replay rebuilt and kernel-checked the complete 13-module notebook dependency closure. The eight new proof objects matched the development build byte for byte. All 28 new public declarations passed the axiom audit against `propext`, `Classical.choice` and `Quot.sound`. Fifteen direct comparisons checked the pinned host, integer and field residues, empty intervals, the finite coset bounds, the realized prime windows and the bound of 435 for the explicit coset modulo 1,009.
