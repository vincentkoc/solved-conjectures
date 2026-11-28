# How often can one integer set give critical cyclic bases?

Let $S\subseteq\mathbb N$ and suppose that for each $\varepsilon>0$,
\[
 |S\cap[0,x)|<(\sqrt2+\varepsilon)\sqrt{x}
\]
at every sufficiently large $x$. The set of **all** positive orders $q$ for which the least labels $S\cap[0,q)$ form an ordinary cyclic two-basis has natural density zero. In particular, the fixed-set reformulation of Green 33 permits infinitely many exact orders, but forces their proportion below $x$ to tend to zero. Green's question about unrestricted finite bases remains open. [`all_exact_orders_density`](Green33NestedOrders.lean) · [Fixed-set equivalence](FIXED-PREFIXES.md) · [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

The conclusion also applies to approximate covers. At increasing positive orders $q_i$, let $A_i\subseteq\mathbb Z/q_i\mathbb Z$ have $|A_i|/\sqrt{q_i}\to\sqrt2$ and $|A_i+A_i|/q_i\to1$. If inserting and deleting $o(\sqrt{q_i})$ least labels transforms $A_i$ into the prefix of a fixed $S$, the set of selected orders has natural density zero. This version assumes size and coverage only along the selected sequence. It permits arbitrary growth of $S$ between those orders. [`edited_prefix_orders_density` and `prefix_orders_density`](Green33NestedOrders.lean)

## The cost of retaining labels

Consider arbitrary seeds $A$ and $B$ at paired orders $n\le m$, using their least nonnegative representatives in the same integer coordinates. Suppose each seed has critical normalized size and the larger seed covers a fraction tending to one as $m\to\infty$. Write $u=\sqrt{n/m}$. Then
\[
 \frac{|A\setminus B|}{\sqrt m}\ \ge\ \sqrt2\,u(1-u)-o(1).
\]
When $n/m\to r>0$ this gives a loss of at least $(\sqrt2(1-\sqrt r)-o(1))\sqrt n$. For example, at $r=1/4$ the larger seed must omit at least half the smaller seed up to a vanishing relative error. The smaller seed needs only the size condition. [`edit_bound` and `proportional_loss`](Green33NestedOrders.lean)

Indeed, every retained label belongs to the initial arc of length $n$ at the larger order. The uniform cyclic arc estimate counts $|B|n/m+o(\sqrt m)$ labels there, uniformly even as the relative width varies. Subtracting this count from $|A|$ proves the loss estimate. [Arc equidistribution](Green33ArcDistribution.lean) · [Finite retained-label inequality](Green33NestedOrders.lean)

## From half the index to natural density

Set $m=q_i$ and $n=q_{\lfloor i/2\rfloor}$, with indices starting at zero. Strict increase and positivity give $i\le2n$ and $i\le2(m-n)$. Consequently
\[
  (i/m)^2\le 4u^2(1-u^2)\le 8u(1-u).
\]
For literal prefixes all the earlier labels survive. For edited prefixes the loss is at most the sum of the two edit counts, which is $o(\sqrt m)$. The loss estimate forces $u(1-u)\to0$, hence $i/q_i\to0$. At an arbitrary cutoff, use the greatest index whose order lies below it to obtain natural density zero. For the full set of exact orders, $2q\le |A|^2+2$ gives the matching lower size bound along its increasing enumeration. [Density proofs](Green33NestedOrders.lean) · [Finite basis size bound](REFLECTION-RIGIDITY.md)

## Verification

Lean 4.33.1 rebuilt and independently kernel-replayed the 17 notebook modules in the final import closure. The 132 printed axiom lists, including the seven declarations in this file, contain only `propext`, `Classical.choice`, and `Quot.sound`. The source comparison checked the ordinary Green 33 predicate definitionally at the pinned revision. Every exact cyclic basis has coverage fraction one, and diagonal summands are allowed throughout. [Lean proof](Green33NestedOrders.lean) · [Pinned declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

A separate enumeration checked the retained-label bound on all 173,740 ordered seed pairs with $1\le n\le m\le8$. It also checked the half-index estimate at all 245,760 indices in the 32,767 nonempty order sequences drawn from $1,\ldots,15$.
