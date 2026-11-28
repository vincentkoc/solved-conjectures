# Green 33 · concentration under independent residue-class shifts

Let $A\subseteq\mathbb Z/N$ be a full two-basis and let $m=2r+1$ divide $N$. For each residue class modulo $m$, translate all its elements by the same independent uniform multiple of $m$. Write $A_h$ for the result and $Y_h=|A_h+A_h|/N$ for its coverage. If $k=|A|$ and $s=\binom{k+1}{2}-N$ is the surplus of unordered pairs, then
\[
\operatorname{Var}_h(Y_h)\ \le\ \frac{rm}{N}(k+3s).
\]
The finite bound also holds for any surjection from a finite abelian group onto the odd cyclic quotient. Repeated summands are included in $s$. [Finite variance bound](Green33FullSlideVariance.lean)

For fixed $m$, along **every** growing full cyclic family with $k/\sqrt N\to\sqrt2$, the variance tends to zero. The earlier mean-coverage formula therefore holds in probability.
\[
Y_h \ \xrightarrow{\ \mathbb P\ }\ 1-(1-1/m)(1-2/m)^r .
\]
For $m=3$ this is $7/9$. At every odd $m\ge3$, the proportion of shifts that are still full bases tends to zero. The zero shift always remains full. There is no hypothesis on the parity of $N/m$ or on representation counts in individual layers. [Probability and full-cover theorems](Green33SlideProbability.lean) · [Exact mean and row product](ODD-QUOTIENT-SLIDES.md)

**Growing quotient orders.** Green 33 is equivalent to the existence of growing full critical witnesses with quotient orders $2i+1$ such that $Y_h$ converges in probability to $1-e^{-1}$. The forward direction selects witnesses separately for each quotient. Their exceptional probability is smaller than the chosen tolerance $1/(i+1)$ before moving the reference value to $1-e^{-1}$. Existence of the original full critical family remains open. [Growing-quotient equivalence](Green33GrowingSlideConcentration.lean) · [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Green, problem 33](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.33)

## Proof of the finite estimate

1. In a target residue class, count pairs of missed targets by their common kernel displacement $d$. Their joint miss probability is a product of overlap densities of the original uncovered supports, averaged over $d$. The same $d$ occurs in every factor. [Second-moment identity](Green33SlideRowMoments.lean)
2. Center the indicator of a support by subtracting its density. Fourier inversion and Parseval bound the sum of absolute errors in its overlap densities by the largest nonconstant character sum. A telescoping product estimate adds these errors over the mixed supports. The diagonal support can have arbitrary autocorrelations because their average is exactly its squared density. [Fourier and overlap estimates](Green33SlideOverlapEnergy.lean) · [Tao, Fourier analysis on finite abelian groups](https://www.math.ucla.edu/~tao/247b.1.07w/notes9.pdf)
3. A kernel character extends to the ambient group. For a nontrivial kernel character, Fourier inversion on the quotient expresses each layer transform as an average of nonconstant ambient transforms. Each squared modulus is bounded by $2s+k$. Passing from ordered pairs of distinct layers to their sum support costs at most $s$, since each repeated mixed sum consumes an ambient surplus pair. Thus each mixed support contributes at most $3s+k$ in count units. [Layer character bounds](Green33LayerTransformBounds.lean) · [Ambient character estimate](Green33FourierStability.lean) · [Mixed-pair budget](Green33QuotientLayerBalance.lean)
4. Each row has $r$ mixed supports and its kernel has $N/m$ elements. Applying the row bound and Cauchy–Schwarz to the average over rows gives the stated variance. For a full critical family, $s/N\to0$ and $k/N\to0$. [Row variance](Green33OddSlideVariance.lean) · [Global bound](Green33FullSlideVariance.lean)

The two-target identity was exhaustively checked on every subset and target row for quotient/kernel orders $(3,2),(3,3),(5,2)$, totaling 6,848 rows. A second enumeration tested the variance inequality on all 12,493 full bases for $(3,2),(3,3),(3,4),(5,2),(7,2)$, using 654,987 shift choices after removing the common translation. There were 2,364 bases with strictly positive coverage variance.

Replay with the notebook runner and target `Green33GrowingSlideConcentration`. Codex assisted with the Lean proofs. The personal notebook records a conditional equivalence and an unconditional finite bound. [Replay instructions](../README.md#replay) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33) · [Open Math Agents search](https://github.com/lefttosolve2/open-math-agents/issues?q=%22Green33.green_33%22)
