# How often can a chosen set of factorial residues occur?

Let $p$ be prime and select any set $A\subseteq\{1,\ldots,p-1\}$ of indices. Write $M=|A|$ and let $K$ be the number of distinct values of $i!\bmod p$ for $i\in A$. For each represented residue, measure the distance from its first selected occurrence to its last. Write $W$ for the sum of these distances, and $R=M-K$ for the number of returns. Then
$$
8(R+1)^3\le9(W+1)^2.
$$
If no two selected values have product $1$ or $-1$ modulo $p$, including a value paired with itself, the leading constant improves, with the finite bound below.
$$
32R^3\le27(W+1)^2.
$$
Both inequalities hold at every prime, including when $A$ is empty. [Finite bounds](Erdos478FactorialReturnConcentration.lean) · [widths and returns](Erdos478ColouredReturnWidths.lean)

## A prescribed set of residues

Take a closed interval $[a,b]\subseteq[1,p-1]$ of length $N=b-a+1$. Choose any set $S$ of $s$ residues and count the $M$ indices at which $i!\bmod p$ belongs to $S$. Then $K\le s$ and $W\le s(N-1)$. The inequalities above hold with $R$ replaced by $\max(M-s,0)$ and $W$ by $s(N-1)$. For the second inequality it suffices that the products of pairs from $S$ avoid $\{1,-1\}$.

For a single prescribed residue $\lambda$ with $\lambda^4\ne1\bmod p$, this gives $32\max(M-1,0)^3\le27N^2$. Over $\mathbb F_p$ at most four residues fail this test, by the degree of $X^4-1$. More generally, if $N$ grows and $s=o(\sqrt N)$, the fraction $M/N$ tends to zero even when both the interval and the target set are chosen separately at every prime. The Lean limit assumes exactly $(s+1)^2/N\to0$ and eventual validity of the interval. [Prescribed-set bounds](Erdos478PrescribedResidueBounds.lean) · [moving-target limit](Erdos478SparseTargetMass.lean)

## Counting the gaps

Within each residue class join consecutive selected occurrences. The $R$ edges have total length $W$ by telescoping. An edge of length $k$ starting at $i$ makes $i$ a root of the degree-$k$ polynomial $\prod_{j=1}^k(X+j)-1$ over $\mathbb F_p$. Each root can be used once across all the selected classes. The canonical positive interval has no edge of length one. [Ordered edges](Erdos478ConsecutiveReturnPairs.lean) · [gap-root bound](Erdos478WindowPairIncidence.lean)

For even $k$, Wilson reflection sends $(i,i+k)$ to $(p-1-i-k,p-1-i)$. The signs in the two Wilson products agree. The reflected pair therefore also collides, and its value times the original value is $1$ or $-1$. The separation hypothesis makes the reflected starts disjoint from the selected starts. It also excludes $(p-1)!=-1$, so the reflected lower endpoint is positive. Thus at most $k/2$ selected returns can use an even gap. [Reflected root count](Erdos478ReflectedReturnRoots.lean)

Add one formal gap of length one. At cutoff $h$, the shortfall of any gap $k<h$ is $h-k$. Charging these shortfalls to the degree capacities gives
$$
6h(R+1)+h\le6(W+1)+h^3.
$$
With the halved even capacities and $h=2t$, the corresponding inequality is $2t(R+1)\le W+1+t^3$. Taking the nearest integer to the real optimizer yields the displayed cubic bounds with their finite endpoint terms. [Capacity sums](Erdos478ReturnCapacitySums.lean) · [integer rounding](Erdos478ReturnCubicBounds.lean)

## Relation to Erdős 478

Garaev, Luca and Shparlinski already prove a uniform $O(N^{2/3})$ upper bound for one residue in Theorem 12, using the degree bound for prescribed small gaps. Here the actual sum of fibre widths accounts for many residues simultaneously. Wilson separation yields a second explicit constant. The notebook's earlier moving-window theorem averages over starting positions. The present bound applies to each chosen interval and each set of targets. [Garaev–Luca–Shparlinski, Theorem 12](https://arxiv.org/pdf/math/0403422) · [earlier moving-window theorem](TypicalFactorialWindows.md)

DeepMind asks whether the cardinality of the entire factorial image divided by $p$ tends to $1-e^{-1}$. The concentration estimates leave that density open. Grebennikov, Sagdeev, Semchankau and Vasilevskii give lower bounds on the whole image and on long intervals. Hu's preprint gives the full-image lower bound $\gg p^{8/15}$. [Pinned statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean) · [Grebennikov et al.](https://doi.org/10.4171/rmi/1422) · [Hu](https://arxiv.org/abs/2608.01781) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [Left to Solve](https://www.lefttosolve.com/p/Erdos478.erdos_478)

## Verification

From the pinned Formal Conjectures checkout, run `lake env python3 "$NOTEBOOK/scripts/replay-research" Erdos478SparseTargetMass`.

Direct enumeration checked 72,321 prime, interval and target-set combinations through $p=61$, including 45,968 satisfying the product separation condition. For each case it checked the individual gap capacities, the total width and the applicable cubic inequalities.

Independent Lean 4.33.1 replay rebuilt and kernel-checked all 80 modules in the dependency closure. Each of the eight new objects matched its development build byte for byte. All 35 public declarations passed the axiom audit against `propext`, `Classical.choice` and `Quot.sound`. Twelve comparisons checked the pinned prime filter, index domain, integer residues, empty intervals and the reflected multiplicity bound of 95 for the residue 2 modulo 1,009.
