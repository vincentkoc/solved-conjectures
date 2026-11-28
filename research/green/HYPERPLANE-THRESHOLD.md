# When a binary sumset contains a hyperplane

Let $A$ be a subset of $\mathbb F_2^n$, with $n\ge 2$. Write $k=\lfloor n/2\rfloor$ and set

$$
h_n=\frac12-\frac{\binom{2k}{k}}{2\cdot 4^k}.
$$

If $|A|/2^n>h_n$, then $A+A$ contains the kernel of a linear functional. A set of density exactly $h_n$ can have a double that misses every affine hyperplane. In dimension four, for example, a five-point set can have a double containing no affine hyperplane. Every six-point set has a double containing a linear hyperplane. [Finite guarantee](Green51Hyperplane.lean) · [Boundary construction](Green51ThresholdExample.lean)

The result evaluates the upper two intervals of the pinned `Green51.guaranteedMaxCosetDim`. Its value is $n-1$ for $h_n<\alpha\le 1/2$ and $n$ for $1/2<\alpha\le1$. At $\alpha\le h_n$ its value is at most $n-2$. In the precise quantifiers of `green_51.one_half`, fixing the codimension allowance at one works for a nonnegative $C$ if and only if $C<1/\sqrt{2\pi}$. At equality the even dimensions already furnish counterexamples. [Lean statements](Green51CosetThreshold.lean) · [Pinned host definitions](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

## Proof

Let $D$ be the directions absent from $A+A$. Choose a basis for their span from $D$. A linear functional taking the value one on all basis vectors either takes that value on all of $D$, or vanishes on some $d\in D$. In the latter case $d$ is a sum of an even number of basis directions. Padding with pairs of $d$ gives $2k$ missing directions whose sum is also missing. They define a linear map from $\mathbb F_2^{2k}$ to the ambient cube. Each translated preimage of $A$ is independent in the graph joining cube neighbours and antipodes. Averaging over translations handles maps of every rank. [Direction and averaging proofs](Green51Hyperplane.lean)

The adjacency eigenvalue at a Walsh character of weight $t$ is $2k-2t+(-1)^t$. Restriction to the complement of an independent set is injective on either strict-sign eigenspace. Counting its characters gives the central-binomial bound. This folded-cube independence number and its inertia proof are classical. Rooney gives the calculation and credits Godsil. [Lean spectral proof](Green53FoldedCube.lean) · [Rooney, *Spectral Aspects of Cocliques in Graphs*, Chapter 4](https://dspacemainprd01.lib.uwaterloo.ca/server/api/core/bitstreams/9e341e30-a231-4891-a7ea-38cc3144dc7c/content)

For sharpness, take the vectors with fewer than $k$ ones in the first $2k$ coordinates. Their double misses the all-ones vector and each of its Hamming neighbours. Every nonempty affine subspace of codimension at most one meets this shell. The Wallis product bounds then distinguish the even-dimensional boundary from its limiting constant. [Hamming-ball proof](Green51ThresholdExample.lean) · [Wallis estimates and limiting threshold](Green51CosetThreshold.lean)

## Three covering sets

If $A,B,C$ cover the cube and $|C|<2^{n\bmod 2}\binom{2k}{k}$, one of $A+A$ and $B+B$ contains a linear hyperplane. Equality allows a partition with both designated doubles missing every affine hyperplane. Take the extremal set and a disjoint translate by a missing direction. Their doubles coincide and the complement has exactly the boundary size. This addresses the size of the third class in a three-colour instance of Green 53. [Covering and equality statements](Green51ThresholdExample.lean) · [Green's problem list](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf)

## Related work

Sanders proved a codimension-one bound near density one half. Kohlmeyer and Kruer subsequently answered the general bounded-codimension question, allowing codimension to depend on $C$. Faldor formalized their proof, and the Left to Solve port proves the general host statement. The finite threshold here specifies exactly when one dimension of loss suffices. [Sanders](https://arxiv.org/abs/1003.5649) · [Kohlmeyer and Kruer](https://liamkruer.com/assets/work/conjectures/problems/green-51/paper/proof.pdf) · [Faldor's Lean proof](https://github.com/maxencefaldor/formal-conjectures/blob/0866dc3e290daac563bf732977abd9281f387220/Solution.lean) · [Left to Solve port](https://github.com/lefttosolve2/open-math-agents/pull/5448) · [DeepMind status proposal](https://github.com/google-deepmind/formal-conjectures/pull/8410)
