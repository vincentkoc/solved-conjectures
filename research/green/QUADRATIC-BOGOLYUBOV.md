# Five sums of every binary quadratic graph contain an input-dimensional flat

Let $f:U\to V$ be a quadratic map of finite binary vector spaces, with $n=\dim U$, $d=\dim V$, and graph $\Gamma$. **Five sums of $\Gamma$ contain an affine subspace of dimension at least $n$.** Its codimension is at most $d=\log_2(1/\operatorname{dens}\Gamma)$. The zero map attains equality for every $n,d$. Three summands give codimension at most $2d$. The function can have arbitrary constant and linear parts. [Graph theorems](Green50QuadraticBogolyubov.lean) · [Zero-map bound](Green50QuadraticDescent.lean)

If $A+A$ contains this graph over complementary subspaces of the ambient cube, the same flat appears in $10A$. The Lean theorem `quadratic_model_green50` gives the pinned Green 50 conclusion with coefficient one whenever $d\le\log_2(1/\operatorname{dens} A)$. The [quotient construction](FUNCTION-GRAPH-REDUCTION.md) always gives an unrestricted function graph at that dimension. Some Hamming balls in arbitrarily large dimensions force every **quadratic** graph in their twofold sumset to use strictly more output dimensions. This follows by applying the fivefold theorem and the existing Hamming-ball obstruction at base two. Green 50 for arbitrary sets remains open. [Model obstruction](Green50QuadraticModels.lean) · [Pinned DeepMind declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/50.lean) · [Green, Problem 50](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#page=25)

A stronger obstruction holds at every fixed density below one half and for every fixed multiple of the logarithmic output dimension. [Polynomial model threshold](POLYNOMIAL-MODEL-THRESHOLD.md)

## The rank estimate

For a finite additive family of alternating scalar forms $Q_z$ on $U$, there is a common totally isotropic subspace of codimension at most twice their mean rank. To see this, choose a nonzero family member $A$ of rank $r$ and restrict all forms to $H=\ker A$. For each member $X$, set $Z=X(H)$, viewing $X$ as a map into the dual. Both $X$ and $X+A$ have images containing $Z$, and their images together span the image of $A$. If $s$ is the rank of $H\to U^*/\operatorname{im} A$ induced by $X$, then $\dim(Z+\operatorname{im} A)=r+s$ and $\dim Z\ge s$. The subspace dimension formula gives
$$r+2s\le \operatorname{rank} X+\operatorname{rank}(X+A).$$
Alternation makes $\operatorname{im} A$ vanish on $H$, so the rank of the restricted form on $H\times H$ is at most $s$. Translation by $A$ permutes the family indices. On averaging, the $r$ lost input dimensions cost at most twice the drop in mean rank. Restrict until the family vanishes and sum these inequalities. [Mean-rank proof](Green50QuadraticRankDescent.lean)

## Choosing two directions

Write $B$ for the polarization of $f$. Choose two independent uniformly sampled directions $a,b$ and set $W=\operatorname{im} B(a,\cdot)+\operatorname{im} B(b,\cdot)$. For a functional $\lambda\in V^*$ let $r_\lambda$ be the rank of $\lambda B$. It annihilates $W$ with probability $4^{-r_\lambda}$. Thus the expected sum of $4^{r_\lambda}$ over the annihilator of $W$ is exactly $2^d$. Choose a pair for which the sum is at most this expectation.

Put $m=\dim W$. The annihilator has $2^{d-m}$ elements, so its mean weight is at most $2^m$. Convexity of the exponential gives $2\,\mathbb E[r_\lambda]\le m$. The Lean proof uses an integer affine lower bound on powers of two. The mean-rank lemma supplies an input subspace $H$ of codimension at most $m$ on which every surviving scalar form vanishes. Dual separation now gives $B(H,H)\subseteq W$.

Over $H$, the map $f$ modulo $W$ is affine. Every point of $W$ is the sum of two polar values, which can be added vertically to $\Gamma$ in five graph summands. Lifting the restricted affine graph along $W$ gives a flat of dimension $\dim H+\dim W\ge n$. The same argument with $k$ sampled directions bounds $k\operatorname{codim}H$ by $2\dim W$ and gives the threefold assertion at $k=1$. [Fibre identity](Green50QuadraticFibres.lean) · [Affine lifting lemma](Green50QuadraticFlats.lean) · [Replay instructions](../README.md#replay)

The number of sums required to fill the whole affine span can still grow with $d$. The exact worst case at fixed $n,d$ is $2\min(\lfloor n/2\rfloor,\lfloor\sqrt d\rfloor)+1$. [Covering-order theorem](QUADRATIC-GRAPH-DIAMETER.md)
