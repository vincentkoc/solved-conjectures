# Five sums of a quadratic graph

Let `f : U → V` be a quadratic map between finite binary vector spaces. Write Γ for its graph, d for the dimension of V, and B for the bilinear polarization of f. If every nonzero linear functional ℓ on V makes the scalar form ℓ∘B have rank at least d/2, then **5Γ = U × V**. Whenever A+A contains such a graph over complementary subspaces, **10A is the whole ambient space**. The function graph constructed for an arbitrary A can have higher degree. [Lean proof](Green50QuadraticGraphs.lean) · [Graph reduction](FUNCTION-GRAPH-REDUCTION.md) · [DeepMind’s Green 50](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/50.lean)

## Counting direction pairs

The fibre of 2Γ above a direction a consists of the values `f(x) + f(x+a)`. For a quadratic map this is a translate of the image of `B(a,·)`. Two directions a and b suffice if the images of `B(a,·)` and `B(b,·)` together span V. Four graph summands then give an entire fibre over a+b. A fifth graph point moves that fibre to any prescribed input.

For a nonzero functional ℓ, let Rℓ be the radical of ℓ∘B. A direction pair fails to span precisely when some ℓ annihilates both images, so the pair lies in Rℓ × Rℓ. Thus it suffices that the sum of |Rℓ|² over all nonzero ℓ be strictly smaller than |U|². Under the stated rank condition, each |Rℓ|² is at most |U|²/2ᵈ. There are 2ᵈ−1 nonzero functionals.

## Why five summands can be necessary

On the four-dimensional binary cube take `f(x) = (x₀x₃, x₁x₂, x₁x₃, x₂x₃)`. The last two coordinate directions together reach all four output coordinates. Four graph points summing to zero in the input have an output consisting of the four minors `(p₀₃, p₁₂, p₁₃, p₂₃)` of a two-row matrix with four columns. The binary Plücker relation `p₀₁p₂₃ + p₀₂p₁₃ + p₀₃p₁₂ = 0` excludes the output `(1,1,0,0)`. Since the graph contains zero, this also rules out each shorter sumset. Each nonzero scalar component contains a cross term with coefficient one. The corresponding two-coordinate restriction of its polarization has rank two, so this example meets the rank condition.
