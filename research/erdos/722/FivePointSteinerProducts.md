# Products of Steiner 3-designs with five-point blocks

For any nonnegative integers $a,b$, ordinary Steiner systems $S(3,5,a+1)$ and $S(3,5,b+1)$ yield an ordinary $S(3,5,ab+1)$. Both inputs and the conclusion use the pinned `Finset.IsBlockDesign 3 5`. This is the five-point case of Wilson’s product theorem for Steiner 3-designs. Mohácsy and Ray-Chaudhuri gave an independent proof for prime-power block size minus one. [Checked specialization](Erdos722FivePointProducts.lean) · [Mohácsy and Ray-Chaudhuri, *Candelabra systems and designs*](https://www.sciencedirect.com/science/article/abs/pii/S0378375802002264) · [Explicit statement of the product theorem](https://www.math.iitb.ac.in/~niranj/papers/newcandelabras.pdf)

The whole five-point block and the cyclic $S(3,5,26)$ therefore give a design at **every** order $1+4^u25^v$, with $u,v\ge0$. Examples with both factors include 101, 401 and 2501. The case $u=v=0$ is the vacuous design at order two. The product theorem also permits a punctured order of zero. The empty design on one point realizes the resulting order one. [Cyclic 26-point seed](Erdos722SecondOrderTwentySix.lean) · [Grannell, Griggs and Phelan](https://doi.org/10.1016/S0304-0208(08)72887-1)

For **every** real $\varepsilon>0$ and every sufficiently large integer $n$, at least one of these explicit orders lies in $[n,(1+\varepsilon)n)$. The theorem provides a design at that order. DeepMind’s rank-three, block-size-five statement asks for a design at *each* sufficiently large admissible order. Keevash proved the general eventual existence theorem. [Relative-interval theorem](Erdos722FivePointProducts.lean) · [Pinned Erdős 722](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/722.lean) · [Keevash](https://arxiv.org/abs/1401.3665)

## The construction

Distinguish a point $\infty$ in each input and write $U,V$ for the remaining points. The product has points $\{\infty\}\cup(U\times V)$. Project a triple onto either coordinate and discard infinity. A single finite value selects its point. Two finite values select the unique block through them and infinity. Three distinct finite values select their unique block. Call a block containing infinity a *line*, and a block avoiding infinity a *circle*. A line has four finite points and a circle has five. These rules give exactly one face in each factor for every product triple. [Unique projected face](Erdos722PointedFaces.lean)

Each pair of selected faces has a rectangle of finite points together with one point at infinity. In a local triple, a point face requires one distinct finite coordinate, a line at least two, and a circle three. A filling uses only five-point blocks whose triples meet both requirements and covers every eligible triple exactly once. Transport the fillings to their rectangles and take their union. Any block containing a given triple must originate in that triple’s uniquely determined rectangle. The local covering property then supplies its unique block. The Lean gluing theorem works for arbitrary block size $q+1$ given the corresponding fillings. [Rectangle geometry](Erdos722PointedTiles.lean) · [Gluing and canonical transport](Erdos722PointedDesignProduct.lean)

## The finite fillings

A point paired with a point has no triples. A point paired with a line takes the full five-point block, including infinity. A point paired with a circle takes the five finite points. The remaining three cases, up to swapping coordinates, each have 60 blocks and 600 eligible triples. A kernel computation checks membership in exactly one block for each eligible triple, zero for the other triples, and five points in every block. [Incidence tables and certificate](Erdos722FivePointTiles.lean)

| Pair of faces | Construction of its 60 blocks |
| --- | --- |
| Line and line | Take the 68 projective images of the subline $\mathbb P^1(\mathbb F_4)$ in $\mathbb P^1(\mathbb F_{16})$. Remove the four coordinate rows and four columns through infinity. |
| Circle and line | Use the graphs of the 60 nonconstant words $P(x)/h(x)$ on $\mathbb P^1(\mathbb F_4)$, for $\deg P\le2$ and monic irreducible quadratic $h$. At infinity take the quadratic coefficient of $P$. |
| Circle and circle | Take the graphs of the 60 even permutations of five elements. A bijection on three prescribed distinct inputs extends to exactly one even permutation. |

To reproduce the tables, number field elements by the binary coefficients of their polynomial representatives. For the first case take $\mathbb F_{16}=\mathbb F_2[g]/(g^4+g+1)$, order the subfield as $(0,1,g^5,g^{10})$, and identify $(i,j)$ with $u_i+g u_j$. The projective maps are $z\mapsto a+bz$ and $z\mapsto a+b/(z+d)$, with $b\ne0$. For the second case take $\mathbb F_4=\mathbb F_2[w]/(w^2+w+1)$, use $h(x)=x^2+x+w$, and place infinity after the four field elements in the circle coordinate. Number each rectangle’s infinity by zero and each finite point by $1+i\cdot(\text{second width})+j$. Sort each block’s five numbers, then sort the blocks lexicographically. Bit $r$ in a point’s incidence row denotes its membership in block $r$. [Earlier projective-subline construction](../Erdos722ProjectiveSublines.lean)

## Why the relative gaps shrink

Dirichlet approximation to $\log(25)/\log(4)$ gives powers with logarithms $u<v$ as close as desired. Equality is excluded because five divides every positive power of 25 and no power of four. Put $d=v-u$ and choose $M$ so that $Md\ge\log 4$. The $M+1$ logarithms $(M-i)u+iv$ span at least $\log 4$ in steps of $d$. Translating by nonnegative multiples of $\log 4$ covers the entire tail with gaps at most $d$. Taking $d<\log(1+\varepsilon)$ and restoring the distinguished point gives the interval theorem. [Checked spacing argument](Erdos722MixedOrderIntervals.lean)

## Replay and comparison

From the pinned Formal Conjectures checkout run `lake env python3 "$NOTEBOOK/scripts/replay-research" Erdos722FivePointProducts`. The DeepMind statement PR, Left to Solve entry and Open Math Agents reduction concern the general existence problem. OMA’s accompanying proof handles rank one. The product and its relative-interval corollary are partial formal results for rank three. [DeepMind statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5495) · [Left to Solve](https://www.lefttosolve.com/p/Erdos722.erdos_722) · [OMA reduction](https://github.com/lefttosolve2/open-math-agents/pull/17505) · [OMA rank-one proof](https://github.com/lefttosolve2/open-math-agents/pull/17952)

The clean Lean 4.33.1 build and independent exact-name kernel replay covered all 26 modules. All 17 public theorem and template declarations use only `propext`, `Classical.choice` and `Quot.sound`. Nine direct checks cover the exact host statement and predicate, the arbitrary product and relative interval, the vacuous orders, and the examples 101, 401 and 2501.
