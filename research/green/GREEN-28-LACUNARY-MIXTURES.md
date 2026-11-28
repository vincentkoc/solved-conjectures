# Green 28 · Approximate uniformity on growing intervals

For every $\varepsilon>0$ there are constants $C,K$ such that for **every** $k\ge K$ one can choose two independent integer laws $P,Q$ whose sum has support $[0,k)$ and satisfies
$$
d_{\rm TV}(P*Q,\operatorname{Unif}[0,k))\le C/k .
$$
Each input has full finite interval support. Each is at distance at least $1-\varepsilon$ from **every** uniform law on a nonempty finite set of integers, allowing the comparison set to have any cardinality or position. [Construction at every length](Green28LacunaryMixtures.lean)

## Separating one input from all uniforms

Mix $n$ uniform laws with equal weights, using sets $A_i$ whose cardinalities grow by factors of at least $n^3$. The sets may overlap. Fix any comparison set $T$ of size $h$. The union $F$ of layers of size at most $h/n^2$ occupies at most $h/n$ sites. A layer of size at least $nh$ puts at most $1/n$ of its mass on $T$. At most one layer lies strictly between these ranges. On the event $T\setminus F$ the comparator has mass at least $1-1/n$ and the mixture has mass at most $2/n$. This gives the bound $1-3/n$. Distance to the family of uniforms on arbitrary subsets also occurs in generalized uniformity testing. [Layer inequality](Green28LacunaryMixtures.lean) · [Batu and Canonne](https://arxiv.org/abs/1708.04696)

## Producing the nearly uniform sum

Write $U_d$ for the uniform law on $[0,d)$. Take layer lengths $d_i=(n^3)^i$, $0\le i<n$, and put $t=d_{n-1}$. Independently draw $A,B$ from the equal mixture of the $U_{d_i}$ and draw $I\sim U_N$, $J\sim U_t$. Set
$$
X=A+tI,\qquad Y=J+tB .
$$
Their marginal layer sizes are $Nd_i$ and $td_i$, so both inputs obey the separation bound. The largest layers give full marginal supports $[0,tN)$ and $[0,t^2)$. Conditional on $A,B$, the sum is a translate of $J+tI$, which is uniform on $tN$ consecutive integers. Every such translate lies inside $[0,tN+t^2-1)$. For any enclosing initial interval of length $k$, the conditional law is at distance at most $1-tN/k$ from its uniform. Mixing preserves this bound. [Finite grid construction](Green28LacunaryMixtures.lean)

For a prescribed $k$, take $N=\lfloor(k-t^2+1)/t\rfloor$. Replace the first input by a uniform draw on $[0,k-t^2+1)$ with probability $1/k$, keeping its original law otherwise. This fills the desired output interval and costs at most $1/k$ in total variation for the first input and its convolution. One can take $n>4/\varepsilon$, $C=t^2+t$ and $K=t^2-1+t+n$. These constants are bounds furnished by the construction. [Every-length theorem](Green28LacunaryMixtures.lean)

## Consequence for exact repair

Every exact factorization of a uniform integer interval has uniform marginals, as shown by Zhigljavsky, Golyandina and Gryaznov. The Lean proof uses the notebook’s reflected-prefix criterion to recover this special case. Applying the construction with $\varepsilon=1/4$ shows that for every positive output tolerance there is an interval example for which **each** input lies farther than $1/2$ from its corresponding factor in **every** exact repair. Thus the fixed-output-budget inverse-stability theorem cannot have a tolerance independent of the budget. [No size-free repair](Green28LacunaryMixtures.lean) · [Exact interval classification](https://doi.org/10.1016/j.spl.2016.06.006) · [Reflected-prefix criterion](GREEN-28-REFLECTED-PREFIX.md) · [Fixed-budget inverse stability](GREEN-28-INVERSE-STABILITY.md)

The pinned Green 28 hypothesis requires the sum to be exactly uniform. These examples give approximate sums, with error measured in total variation. The earlier approximate-interval examples control relative error at each output and compare inputs to the uniforms on their own supports. Here all possible comparison supports are covered. [Pinned declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean) · [Earlier interval examples](GREEN-28-NEAR-UNIFORM-INTERVAL.md)

The source check covered the DeepMind issue and statement PR, Left to Solve, the OMA reductions and special cases, and the personal notebook. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28) · [OMA first reduction](https://github.com/lefttosolve2/open-math-agents/pull/9606) · [OMA second reduction](https://github.com/lefttosolve2/open-math-agents/pull/21793) · [Two-site case](https://github.com/lefttosolve2/open-math-agents/pull/27234) · [Degree-five case](https://github.com/lefttosolve2/open-math-agents/pull/29600)

A fresh source build and independent Lean 4.33.1 kernel replay checked all 14 notebook modules. All 107 axiom reports listed only `propext`, `Classical.choice` and `Quot.sound`. Replay `Green28LacunaryMixtures` with the [notebook runner](../../scripts/replay-research).
