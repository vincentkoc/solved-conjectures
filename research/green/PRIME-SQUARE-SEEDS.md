# Exactly uniform sums at prime-square order

Let $p$ be prime. Of the $\binom{p^2}{2p-1}$ subsets of $\mathbb Z/p^2$ with $2p-1$ elements, **exactly $p^p$** can support two independent draws whose sum is uniform. Each such seed consists of one full residue class modulo $p$ and one point from every other class. The count distinguishes subsets of the labeled group, including their different translates. [Classification and count](Green33PrimeSquareSeeds.lean)

Every pair of laws giving a uniform sum on such a seed has the following description, after possibly exchanging the draws. The first is uniform on the full class. The second assigns mass $1/p$ to each of the other $p-1$ points and divides its remaining mass $1/p$ arbitrarily among the $p$ elements of the full class. Conversely every such division works, including divisions with zero weights. Both inputs may use arbitrary real probabilities. The earlier square-order lower bound makes $2p-1$ the minimum common budget. [Law classification](Green33PrimeSquareSeeds.lean) · [Square-order lower bound and equality](SQUARE-ORDER-TILINGS.md)

## Proof

At minimum common size, exact uniformity forces one input to be fair on $p$ labels by the square-order theorem. Its weights are rational. The prime-power cyclotomic argument then makes at least one of the two extended weight functions periodic under subtraction of $p$. That weight is constant on each residue class modulo $p$. A nonzero class uses $p$ labels, and two such classes would use $2p$. The periodic weight is therefore uniform on one entire class. [Fair-input theorem](Green33SquareTilings.lean) · [Cyclotomic periodicity](Green33PrimePowerBudget.lean)

Write $c$ for that class, $Q$ for the other law and $R$ for the sum. Direct convolution gives
\[
 R(z)=\frac1p\sum_{y\equiv z-c\pmod p}Q(y).
\]
Thus $R$ is uniform precisely when every quotient class has $Q$-mass $1/p$. This proves the necessity of a full class and a representative of each other class. For sufficiency choose a uniform first draw on the full class and a uniform second draw on a transversal contained in the seed. [Block convolution and seed criterion](Green33PrimeSquareSeeds.lean)

There are $p$ choices of the full class and $p$ choices of a point in each of the other $p-1$ classes. Two distinct full classes would already exceed the budget, so each resulting seed has a unique parameterization. Exhaustive enumeration of pairs of $p$-element tiles independently recovers all four seeds modulo 4 and all 27 seeds modulo 9. [Parameterization and enumeration theorem](Green33PrimeSquareSeeds.lean)

## Sources and scope

Fan, Fan and Shi characterize tiles of cyclic prime-power groups by $p$-homogeneous trees in Theorem 4.2. For order $p^2$, a tile of size $p$ branches at exactly one of the two digit levels. Zhukov gives a recursive description of tilings in cyclic $p$-groups. The statements here concern the **common support and all real probability laws** at the minimum budget. The unweighted tiling structure is classical. [Fan, Fan and Shi, §4](https://arxiv.org/pdf/1511.04837) · [Zhukov, *Tilings of p-ary cyclic groups*](https://www.mathnet.ru/eng/semr448)

Green 33 asks for ordinary sumset coverage with normalized size tending to $\sqrt2$ along unbounded orders. Exact uniformity of the sum law is stronger, and its minimum normalized size here is $2-1/p$. The pinned question remains open. The DeepMind issue closed with the statement formalization. Left to Solve listed no solution, and targeted searches of DeepMind, Open Math Agents and the personal notebook identified no matching Lean classification. [Pinned source](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33) · [Open Math Agents search](https://github.com/lefttosolve2/open-math-agents/issues?q=%22uniform+sum%22+%22prime-square%22)

Replay **Green33PrimeSquareSeeds** with the [notebook runner](../../scripts/replay-research). The nine-module closure was rebuilt in Lean 4.33.1 and independently checked by the kernel. All 84 printed axiom sets use only standard axioms.
