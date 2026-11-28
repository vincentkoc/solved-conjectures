# Green 33 through prefixes of one integer set

There exists a set $S\subseteq\mathbb N$ whose prefixes give exact two-bases modulo infinitely many positive integers and whose global counting limsup attains the optimum over unrestricted finite cyclic bases. Write $K_S(x)=|S\cap[0,x)|$ and let $\gamma$ be the common limit of the maximal strict and ordinary cyclic orders divided by the square of the size budget. Then the same set satisfies
\[
\limsup_{x\to\infty}\frac{K_S(x)}{\sqrt{x}}=\frac1{\sqrt\gamma},
\qquad
\liminf_{x\to\infty}\frac{K_S(x)}{\sqrt{x}}=0,
\qquad
\sqrt2\le\frac1{\sqrt\gamma}\le\frac{18}{\sqrt{130}}.
\]
Both limits range over every integer cutoff. The exact basis condition at a selected order $q$ uses only the least labels $S\cap[0,q)$, reduced modulo $q$, and permits a repeated summand. The numerical value of the optimum is open. [Lean declarations](Green33FixedPrefixes.lean) · [Maximal orders and their limit](MAXIMAL-ORDERS.md) · [Graham–Sloane, §1](https://doi.org/10.1137/0601045)

Green 33 is equivalent to the existence of such a set with counting limsup $\sqrt2$ and liminf zero. Its original quantifiers allow a fresh finite set at each order. The theorem `green_iff_one_set` retains the absolute tolerance, frequency at infinity, positive moduli, and ordinary cyclic sumset of the pinned declaration. Earlier work gives a stronger lower bound $\sqrt{8/\pi}$ when the normalized count converges. The zero liminf in the present construction permits the oscillation needed below that threshold. [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Regularly growing truncations](REGULAR-TRUNCATIONS.md)

## A cyclic cut and the gaps between stages

For a seed $A$ of size $k$ modulo $q$, use the walk with increment $q\,1_A(i)-k$ at site $i$. Its total over one period is zero. Start at a maximum of its partial sums and call the translated least labels $B$. Every subsequent partial sum up to one period is nonpositive, including after a wrap. Thus
\[
q\,|B\cap[0,x)|\le kx\qquad(0\le x\le q).
\]
For $x\le q$ the count is at most $(k/\sqrt q)\sqrt x$ and the same bound holds for $x\ge q$ by the total size. If $kK<q$, the first $K$ sites are empty. Translation takes the sumset to a translate, so full coverage survives the choice of origin. [`balanced_cut` and the translated basis proof](Green33FixedPrefixes.lean)

Suppose each positive tolerance $\varepsilon$ admits arbitrarily large full bases with $k/\sqrt q<c+\varepsilon$. After choosing the $j$th order $q_j$, take the next stage beyond the cutoff $h_{j+1}=((j+2)(q_j+1))^2$. The cut above lets us keep every new label at least $h_{j+1}$ and the entire new block below its own order. Their union defines $S$. For $h_{j+1}\le x<h_{j+2}$ the old labels contribute at most $q_j/\sqrt x\le1/(j+2)$ to the coefficient, and the new block contributes at most $c+1/(j+2)$. At $x=h_{j+1}$ only the old labels contribute. At $q_j$ the prefix contains the whole $j$th basis. This proves the uniform upper bound, the subsequence tending to zero, and the unbounded sequence of exact bases. [`fixed_prefixes` and `feasible_iff_fixed`](Green33FixedPrefixes.lean)

The maximal-order limit identifies the feasible coefficients as exactly the closed interval $[1/\sqrt\gamma,\infty)$. Indeed, maximal orders at each sufficiently large budget supply witnesses, and any full basis of size $k$ has order at most the maximal order at that budget. Applying the construction at the endpoint attains it. The lower bound follows from $2q\le k^2+2$. The upper bound uses the notebook's verified lift of the 18-label order-130 seed, affinely equivalent to zero and the generators of the degree-17 graph in Lewis's table 5. [`optimal_fixed_set` and `optimal_bounds`](Green33FixedPrefixes.lean) · [Finite lower bound](REFLECTION-RIGIDITY.md) · [Seed and lift](QUARTIC-SEED.md) · [Lewis, table 5](https://arxiv.org/pdf/1506.02844#page=14)

## Verification

Lean 4.33.1 rebuilt and independently kernel-replayed the 11 notebook modules in the import closure. All 88 printed axiom lists, including the seven declarations here, use only `propext`, `Classical.choice`, and `Quot.sound`. A separate definitional-equality check compared the type of `Green33.green_33` at the pinned revision with `Green33StrictReduction.OrdinaryLimit`. An independent enumeration checked all 8,190 subsets at orders 1 through 12, covering 98,304 prefix inequalities. It also checked the translated sumset for each subset, including all 4,354 full bases. [Lean proof](Green33FixedPrefixes.lean) · [Pinned declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)
