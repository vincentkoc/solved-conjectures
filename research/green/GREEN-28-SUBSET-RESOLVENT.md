# Green 28 · Testing factor widths over a finite field

Let $S$ be a nonempty finite set of integers, $s=|S|$, and $d=\max S-\min S$. Write $H(X)=\sum_{a\in S}X^{a-\min S}$. Put $m=\operatorname{lcm}(1,\ldots,d)$ with the empty lcm equal to one. Choose a prime $p$ satisfying
$$
p^2>4^{\binom d{\lfloor d/2\rfloor}} s^{\binom {d-1}{\lfloor(d-1)/2\rfloor}}.
$$
Here $d-1$ is truncated at zero. For **every** positive $k$, the polynomial $H$ has a complex monic factor of degree $k$ and constant term one exactly when its reduction has such a factor over $\mathbb F_{p^m}$. The same prime and extension work for all widths and all output masks of this degree and size. The test permits repeated roots. A factor can be specified by its $k+1$ coefficients. The bounds give a finite test and grow rapidly. [`finite_test_for_mask` and `factor_iff_vectors`](Green28SubsetResolvent.lean)

For the original independent integer laws, excluding every width $0<2k<d$ at **any** single prime forces one marginal to be a point mass and both to be uniform. Conversely, a prime giving this certificate exists exactly when every one of those widths is absent over the complex numbers. These implications classify the reach of this particular certificate. A complex factor can have nonreal or negative coefficients. An actual probability decomposition has stronger constraints. [`pure_of_finite_test`, `uniform_of_finite_test` and `complex_exclusion_iff_one_prime`](Green28SubsetResolvent.lean)

## The integer behind the test

Write a monic integer polynomial as $H(X)=\prod_{i=1}^d(X+\beta_i)$ in a splitting field, with repeated roots assigned different positions. For an integer $z$, set
$$
D_k(H,z)=\prod_{|U|=k}\left(z-\prod_{i\in U}\beta_i\right).
$$
The product is symmetric in the signed roots. The fundamental theorem of symmetric polynomials and Vieta's formulas express it as an integer polynomial in the coefficients of $H$. Its value therefore specializes with those coefficients in every characteristic. Over a splitting field, $D_k(H,z)=0$ is equivalent to a monic degree-$k$ factor with constant term $z$. Each irreducible factor modulo $p$ has degree at most $d$, so it splits in the stated common extension. The exact finite-field condition is $p\mid D_k(H,z)$. In particular, if the complex factor does not exist, the primes that give a false positive are exactly the prime divisors of a nonzero integer. [`value_zero_iff_of_splits` and `finite_factor_iff_dvd`](Green28SubsetResolvent.lean)

The product-of-roots construction is classical. It amounts to evaluating the characteristic polynomial of the multiplicative compound of a matrix with eigenvalues $\beta_i$. Pereira and Vali discuss the compound spectrum and bounds for individual products of roots. The Lean proof uses symmetric polynomials directly. [Pereira and Vali, *Generalizations of the Cauchy and Fujiwara bounds for products of zeros of a polynomial*](https://journals.uwyo.edu/index.php/ela/article/download/1699/1699/1699)

## Bounding the prime

For $k>0$ each factor in $D_k$ has absolute value at most $(|z|+1)\prod_{i\in U}\max(1,|\beta_i|)$. Each position belongs to exactly $\binom{d-1}{k-1}$ subsets of size $k$. This gives
$$
|D_k(H,z)|\le (|z|+1)^{\binom dk}\,M(H)^{\binom{d-1}{k-1}},
$$
where $M(H)$ is the Mahler measure. Landau's inequality bounds $M(H)$ by the Euclidean norm of the coefficient vector. The shifted mask has exactly $s$ nonzero coefficients, all ones. With $z=1$, squaring the bound gives $D_k(H,1)^2\le 4^{\binom dk}s^{\binom{d-1}{k-1}}$. Taking the largest binomial coefficient in each row yields the single prime bound above. [`value_bound_mahler` and `mask_value_bound`](Green28SubsetResolvent.lean) · [Mathlib formalization of Landau's inequality](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Polynomial/MahlerMeasure.html#Polynomial.mahlerMeasure_le_sqrt_sum_sq_norm_coeff)

## Scope and verification

The pinned statement asks for fairness of both marginals when the finite independent sum is uniform on its range. Their normalized polynomials are monic, have nonnegative real coefficients and constant term one, and multiply to the shifted output mask. If both have positive degree, their degrees differ because opposite endpoint pairs would otherwise contribute twice to one binary coefficient. The smaller degree is therefore one of the widths covered by the exclusion certificate. [Normalized factorization](Green28PrimitiveSupport.lean) · [Unequal widths](Green28AlgebraicWidth.lean) · [Pinned Green 28](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean)

The DeepMind issue and statement PR, Left to Solve entry, OMA reductions, two-site submission and personal notebook were checked for an existing formalization. The general problem remains open. Hare's computations concern coefficient patterns of nonnegative factors. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28) · [First OMA reduction](https://github.com/lefttosolve2/open-math-agents/pull/9606) · [Second OMA reduction](https://github.com/lefttosolve2/open-math-agents/pull/21793) · [Two-site submission](https://github.com/lefttosolve2/open-math-agents/pull/27234) · [Hare, *Computational progress on the unfair 0–1 polynomial conjecture*](https://arxiv.org/abs/2307.07363)

A clean source build and independent Lean 4.33.1 kernel replay checked all five notebook modules. All 50 axiom reports listed only `propext`, `Classical.choice` and `Quot.sound`. Replay `Green28SubsetResolvent` with the [notebook runner](../../scripts/replay-research) in the pinned Lean 4.33.1 environment.
