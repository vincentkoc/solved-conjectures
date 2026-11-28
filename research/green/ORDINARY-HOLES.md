# Ordinary sumset holes force losses at cyclic orders

For a fixed $S\subseteq\mathbb N$, let $A_q=(S\cap[0,q))\bmod q$. Call $q$ exact if $A_q+A_q=\mathbb Z/q\mathbb Z$, permitting repeated summands. Let $L(X)$ be the arithmetic mean, over $q=1,\ldots,X$, of $1-|A_q+A_q|/q$. Every $S$ attaining the optimal upper counting coefficient for unrestricted finite cyclic two-bases satisfies
\[
 \overline d(\{q:q\text{ is exact}\})\le \frac{81\pi}{260}<0.979,
 \qquad
 \liminf_{X\to\infty}L(X)\ge\frac12\left(1-\frac{81\pi}{260}\right)^2>0.000226.
\]
The finite-basis optimum is attained by one fixed set. Its value remains unknown. These two bounds apply to every such set, independently of whether the optimum equals $\sqrt2$. At that endpoint the earlier zero-density theorem gives a stronger bound on exact orders. [`optimal_deficits`](Green33OrdinaryHoles.lean) · [Fixed-set attainment](FIXED-PREFIXES.md) · [Critical exact orders](NESTED-ORDERS.md) · [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

## Two holes in the integers

Write $H=\mathbb N\setminus(S+S)$ and $H(x)=|H\cap[0,x)|$. A residue $a<q$ can be represented by a pair of least labels only at the integer sum $a$ or $a+q$. If both lie in $H$, the residue is missing modulo $q$. Fixing a single $a\in H$ sends every $b\in H$ with $b>2a$ to the unsuccessful order $b-a$. These orders are distinct. After a fixed additive boundary error in the counts, the exact orders therefore have upper density at most the upper density of $S+S$. [`missing_residue`, `exact_count`, and `exact_density`](Green33OrdinaryHoles.lean)

Keeping all such pairs yields a bound for how much the prefixes miss. Charge each pair $a,b\in H$, $2a<b<X$, to its order $q=b-a$ and residue $a$. Its weight $1/b$ is at most the missing fraction $1/q$ it accounts for. No two pairs have the same order and residue. If $D_q=|\{a<q:a,a+q\in H\}|$, this gives the finite certificate
\[
 \sum_{\substack{b\in H\\0<b<X}}\frac{H(\lceil b/2\rceil)}b
 \ \le\ \sum_{q=1}^{X-1}\frac{D_q}q.
\]
If $h=\underline d(H)$, every $0<d<h$ gives $H(y)\ge dy$ for all sufficiently large $y$. Each sufficiently large hole $b$ thus contributes at least $d/2$, and there are at least $dX-O(1)$ such holes below $X$. Letting $d$ increase to $h$ proves $\liminf L(X)\ge h^2/2$. This transfer allows arbitrary $S$. [Finite certificate and mean bound](Green33OrdinaryHoles.lean)

## The size coefficient and the Stöhr bound

Assume $|S\cap[0,x)|<(c+\varepsilon)\sqrt{x}$ eventually for every positive $\varepsilon$. For $a>c$, rank each element by the number of smaller elements of $S$. The squared rank of $z$ is at most $a^2z+K^2$ for a fixed $K$. The two ranks of a pair with ordinary sum below $X$ thus lie in the nonnegative quarter disk of squared radius $a^2X+2K^2$. Each represented sum outside the diagonal image uses at least two ordered points. The diagonal correction is $O(|S\cap[0,X)|)=o(X)$. Counting lattice points by the quarter-disk area and then taking $a\downarrow c$ gives
\[
 \overline d(S+S)\le \pi c^2/8,
 \qquad
 \liminf L(X)\ge \tfrac12\max(0,1-\pi c^2/8)^2.
\]
Consequently any sequence of averaging cutoffs along which the mean loss tends to zero requires $c\ge\sqrt{8/\pi}$. Stöhr's classical lower bound concerns an ordinary integer basis. Here the hypothesis is on average modular coverage, and the normalized counting function may oscillate. The numerical corollary uses the verified upper coefficient $18/\sqrt{130}$ from the lift of the Erskine–Lewis seed. [`sumset_density`, `coefficient_loss`, and `mean_full_threshold`](Green33OrdinaryHoles.lean) · [Nathanson, *Cassels Bases*, theorem 4](https://www.theoryofnumbers.com/melnathanson/pdfs/nath2010-138.pdf) · [Quarter-disk count](Green33RegularTruncations.lean) · [Order-130 seed and attribution](QUARTIC-SEED.md)

## Verification

Lean 4.33.1 rebuilt and independently kernel-replayed the 18 notebook modules in the import closure. The 143 axiom reports, including the 11 declarations here, use only `propext`, `Classical.choice`, and `Quot.sound`. A separate check matched the pinned declaration's type by definitional equality and showed that its full ordinary sumset hypothesis gives zero loss for a cyclic prefix. Exhaustive enumeration of all 2,048 subsets of $[0,11)$ tested the weighted-hole, rank-disk, and exact-order count inequalities at each of the 12 cutoffs from 0 through 11. [Lean proof](Green33OrdinaryHoles.lean) · [Pinned declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)
