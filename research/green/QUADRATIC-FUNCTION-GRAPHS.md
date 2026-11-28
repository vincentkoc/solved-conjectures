# Five sums of a quadratic graph

Let `f : U → V` be a quadratic map between finite binary vector spaces. Write Γ for its graph, d for the dimension of V, and B for the bilinear polarization of f. If every nonzero linear functional ℓ on V makes the scalar form ℓ∘B have rank at least d/2, then **5Γ = U × V**. Whenever A+A contains such a graph over complementary subspaces, **10A is the whole ambient space**. The function graph constructed for an arbitrary A can have higher degree. [Lean proof](Green50QuadraticGraphs.lean) · [Graph reduction](FUNCTION-GRAPH-REDUCTION.md) · [DeepMind’s Green 50](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/50.lean)

## Counting direction pairs

The fibre of 2Γ above a direction a consists of the values `f(x) + f(x+a)`. For a quadratic map this is a translate of the image of `B(a,·)`. Two directions a and b suffice if the images of `B(a,·)` and `B(b,·)` together span V. Four graph summands then give an entire fibre over a+b. A fifth graph point moves that fibre to any prescribed input.

For a nonzero functional ℓ, let Rℓ be the radical of ℓ∘B. A direction pair fails to span precisely when some ℓ annihilates both images, so the pair lies in Rℓ × Rℓ. Thus it suffices that the sum of |Rℓ|² over all nonzero ℓ be strictly smaller than |U|². Under the stated rank condition, each |Rℓ|² is at most |U|²/2ᵈ. There are 2ᵈ−1 nonzero functionals.

## Why five summands can be necessary

On the four-dimensional binary cube take `f(x) = (x₀x₃, x₁x₂, x₁x₃, x₂x₃)`. The last two coordinate directions together reach all four output coordinates. Four graph points summing to zero in the input have an output consisting of the four minors `(p₀₃, p₁₂, p₁₃, p₂₃)` of a two-row matrix with four columns. The binary Plücker relation `p₀₁p₂₃ + p₀₂p₁₃ + p₀₃p₁₂ = 0` excludes the output `(1,1,0,0)`. Since the graph contains zero, this also rules out each shorter sumset. Each nonzero scalar component contains a cross term with coefficient one. The corresponding two-coordinate restriction of its polarization has rank two, so this example meets the rank condition.

## An affine subspace for every quadratic map

With no rank assumption, five sums of any quadratic graph contain an affine subspace of codimension at most `⌊(d+2)²/8⌋`. The same bound holds for ten sums of any A whose twofold sumset contains that graph over complementary subspaces. Green 50 asks for a linear bound in the logarithm of the reciprocal density. [Rank-descent proof](Green50QuadraticDescent.lean)

If the high-rank hypothesis fails, choose a nonzero scalar component with polarization of rank r < d/2. A maximal subspace H on which this alternating form vanishes equals its orthogonal complement, so H has codimension r/2. On H the selected component of f is affine. Subtract its constant and linear parts there and project the output to the kernel of the functional. This leaves a quadratic map with one fewer output coordinate. Its graph embeds linearly in the normalized original graph, at ambient codimension r/2 + 1.

The resulting budget obeys `b(0)=0` and `b(d+1)=b(d)+⌊d/4⌋+1`. Solving the recurrence gives the displayed bound. For independent blocks the fivefold sumset is the product of the fivefold sumsets, so the block budgets add. When every output block has dimension at most four, the total codimension is at most the total output dimension, for arbitrarily many blocks. The zero map attains this coefficient since its graph is already a subspace.
