# The next density interval for Green’s coset dimension

For even $n=2s+2$, put $h_{2s}=\tfrac12-\binom{2s}{s}/(2\cdot4^s)$. On the interval
$
h_{n-2}<\alpha\le h_n
$
Green’s guaranteed affine coset dimension is exactly $n-2$. Every set of density at least $\alpha$ has a double containing a **linear** subspace of dimension at least $n-2$. The Hamming ball at the upper endpoint rules out a larger guarantee, even for affine subspaces. In dimension six this determines the answer for minimum set sizes 21 and 22 out of 64. [Lean theorem](Green51CodimensionTwo.lean) · [Pinned definition](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

## The missing directions

Write $D=\mathbb F_2^n\setminus(A+A)$. Above density $h_{n-2}$, either the double contains a linear hyperplane or there is a basis $B$ with
$
D=B\cup\left\{\sum_{b\in B}b\right\}.
$
In the second case there are exactly $n+1$ missing vectors. Send one basis element to $(1,1)$ and all the others to $(1,0)$. The linear map takes every missing vector to a nonzero element of $\mathbb F_2^2$, so its kernel lies in the double. [Classification and count](Green51MissingDirections.lean) · [Projection and exact interval width](Green51CodimensionTwo.lean)

The strict lower endpoint matters for this classification. Take all vectors with fewer than $s$ ones in the first $2s$ coordinates and let the last two coordinates vary freely. This set has density exactly $h_{n-2}$ and its double misses every affine hyperplane. For $s\ge1$ the missing vectors have active weight $2s-1$ or $2s$, giving $4(n-1)$ missing directions. In dimension six these are 20 missing directions, compared with seven just above the boundary when there is no hyperplane. The construction establishes sharpness for the classification. The lower endpoint of the full range where the guaranteed dimension equals $n-2$ is a separate question. [Hamming cylinder and exact count](Green51ThresholdExample.lean)

## Why the density determines the directions

If $D$ is contained in the level one set of a linear functional, its kernel works. Otherwise, choosing a basis of the span of $D$ from $D$ produces an even subset of basis vectors whose sum is also missing. Any such relation of length at most $n-2$ before including the total sum would pull $A$ back, after translation, to independent sets in a folded cube of dimension $n-2$. The folded-cube independence bound then gives density at most $h_{n-2}$. The remaining relation uses an entire basis $B$. An extra missing vector would give a shorter relation by summing its basis support or the complement of that support together with $\sum B$. [Folded-cube averaging](Green51Hyperplane.lean) · [Previous sharp hyperplane threshold and spectral attribution](HYPERPLANE-THRESHOLD.md)

This algebraic argument has a classical graph interpretation. Beaudou, Naserasr and Tardif show that a binary Cayley graph of odd girth $2s+1$ contains the projective cube of dimension $2s$. Mančinska, Pivotto, Roberson and Royle give an induced-subgraph form in Lemma 4.5. At maximal odd girth in even rank the induced cube already occupies every vertex. The finite density interval above applies this structure to Green’s extremal function. The general bounded-codimension result at density $1/2-O(1/\sqrt n)$ is due to Kohlmeyer and Kruer, with a formal proof by Faldor. [Beaudou–Naserasr–Tardif, Theorem 1.5](https://www.irif.fr/~reza/pdfs/papers/BNT15.pdf) · [Mančinska et al., Lemma 4.5](https://arxiv.org/pdf/1808.02051) · [Kohlmeyer–Kruer](https://liamkruer.com/assets/work/conjectures/problems/green-51/paper/proof.pdf) · [Formal proof](https://github.com/lefttosolve2/open-math-agents/pull/5448)
