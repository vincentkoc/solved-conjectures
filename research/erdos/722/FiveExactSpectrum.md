# The exact five-point pair-design spectrum

For every natural number $n$, there is a family `H : Finset (Finset (Fin n))` with `H.IsBlockDesign 2 5` exactly when
$$
n=0\quad\text{or}\quad n\equiv 1,5\pmod{20}.
$$
This is Hanani's classical five-point spectrum, with the vacuous orders of the pinned predicate included. The empty family works on zero or one point. For every $n$, existence is equivalent to the original two binomial divisibility conditions. In particular the specialization $r=2$, $k=5$ requires no lower cutoff. The previous notebook construction supplied all admissible orders from 12801 onward. [Exact statements](Erdos722FiveExactSpectrum.lean) · [Earlier cutoff](FiveSpectrum.md) · [Pinned Erdős 722](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/722.lean) · [Hanani](https://doi.org/10.1016/0012-365X%2875%2990040-0)

## From finite seeds to all orders

Write $n=4u+1$. A master is a pairwise balanced design on $u$ points. A block of size $s$ can be used when a five-point design on $4s+1$ points is available. Deleting one point from that local design yields $s$ groups of four. Inflating the master replaces each point by four points and adjoins a single shared point. This gives a five-point design on $n$ points. [Deletion and inflation](../Erdos722QuartetDeletion.lean)

For $a=0,1$, truncating a sixth column and filling groups gives a master on $5t+r+a$ points from masters on $t+a$ and $r+a$, with $0\le r\le t$. Six initial group counts were already covered. Sixteen more suffice. Below 900 the kernel checks all admissible group counts, trying at most nine values of $t$ for each. At $u\ge900$, take $t=30\lfloor(u-5)/150\rfloor+1$ and $r=u-5t$. Both new column counts are smaller and admissible. Strong induction covers every $u\equiv0,1\pmod5$. [Finite reduction](Erdos722FiveFiniteReduction.lean) · [Transversal fillings](Erdos722FiveMaster.lean) · [Seed assembly](Erdos722FiveExactSpectrum.lean)

| Additional group counts $u$ | Construction |
| --- | --- |
| 11, 36 | At orders 45 and 145, translate a relative difference family on five layers and fill each fiber with its five-point block. |
| 15, 20, 35, 40, 70 | Develop ordinary difference families at orders 61, 81, 141, 161 and 281. |
| 21, 41, 45 | A five-point design on $u$ points already gives a master since five is an allowed block size. |
| 71, 75, 76 | Five-column orthogonal arrays of orders 14 and 15 give $5\cdot14+1$, $5\cdot15$ and $5\cdot15+1$. |
| 116, 120, 121 | Over the field of order eleven, retain ten full columns and take 6, 10 or 11 points from an eleventh column. |

## Checking the ingredients

Smith's five-layer construction uses the four rotations of a nonzero field element. At orders 45 and 145 the additive groups of the layers are $(\mathbb Z/3)^2$ and $\mathbb Z/29$. Each oriented difference outside the kernel of the layer projection occurs exactly once, so translates cover the pairs across fibers. The fibers themselves cover the remaining pairs. At order 81 the four starters are Hanani's, reproduced by Smith. The 141- and 161-point cyclic data occur in the SageMath design database. At 281 the fourteen multipliers $3^{10j}$, $0\le j<14$, applied to $\{0,1,184,24,209\}$ give the starters. Lean checks all 280 nonzero differences. [Relative starters](Erdos722FiveRelativeSeeds.lean) · [Ordinary starters](Erdos722FiveDifferenceSeeds.lean) · [Smith, Theorem 24 and Lemma 28](https://argilo.net/files/bibd.pdf) · [SageMath design database](https://github.com/sagemath/sage/blob/develop/src/sage/combinat/designs/database.py)

The two orthogonal arrays use three Latin squares each, from the order-14 and order-15 data shared by Ian Wanless. Todorov gave the first construction of four mutually orthogonal Latin squares of order 14. For each projection onto two distinct columns, Lean checks that every ordered pair occurs. Equality of the row count and the pair count gives uniqueness. [Arrays and group fillings](Erdos722FiveOrthogonalArrays.lean) · [Finite projection certificates](Erdos722FiveLatinSeeds.lean) · [Todorov](https://doi.org/10.1002/jcd.21298) · [SageMath data and attributions](https://doc.sagemath.org/html/en/reference/combinat/sage/combinat/designs/database.html)

## Scope and replay

The live comparison on 2026-11-28 found the general Erdős statement in DeepMind and the existing-proof target in Left to Solve. OMA's general assembly requires absorption hypotheses. Its rank-one contribution proves a partition result. The personal notebook's earlier five-point theorem had a cutoff. The result here formalizes a classical specialization. Keevash proved the general existence theorem in the literature. [DeepMind statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5495) · [Left to Solve](https://lefttosolve.com/p/Erdos722.erdos_722) · [OMA assembly](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17505) · [OMA rank-one result](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17952) · [Earlier notebook PR](https://github.com/vincentkoc/solved-conjectures/pull/124) · [Keevash](https://arxiv.org/abs/1401.3665)

The scoped Lean 4.33.1 replay rebuilds the 20 modules needed by the exact five-point theorem and also checks the earlier quadruple spectrum, 37 modules in total. Each receives a separate `leanchecker` invocation. The replay audits 21 named declarations and checks all 116 printed axiom reports. It permits `propext`, `Classical.choice` and `Quot.sound`. A separate comparison imports the pinned problem statement and checks the all-order construction against `type_of% (Erdos722.erdos_722 2 5 (by decide) (by decide))` on its original filter. [Notebook replay](../../README.md#replay)
