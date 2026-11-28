# Green 33 · Exact uniform sums with real weights on prime cycles

Let $b(p)$ be the minimum size of a set $A\subseteq\mathbb Z/p$ on which two independent probability laws can have an exactly uniform sum. The laws may differ and may use arbitrary real weights. For every odd prime,
\[
 \frac{p+1}{2}\le b(p)\le\frac{p+5}{2}.
\]
Consequently $b(p)/p\to1/2$ along the primes. When $p\equiv3\pmod4$, **$b(p)=(p+3)/2$**. For example, the exact minima at orders 7, 11 and 19 are 5, 7 and 11. For primes $1\bmod4$ the interval leaves up to two labels undetermined. [Minimum, limit and exact congruence-class theorem](Green33RealBudget.lean)

Green's pinned conjecture asks for full sumset coverage at size $(\sqrt2+o(1))\sqrt M$ along unbounded cyclic orders. Its weighted equivalent allows the sum law to approach uniform in total variation. Here uniformity is exact, which costs a linear number of labels on primes. If even one marginal is required to be rational, the earlier prime-power theorem gives $b(p)=p$. [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Weighted equivalence](WEIGHTED-STABILITY.md) · [Rational-marginal budget](PRIME-POWER-BUDGET.md)

## Construction on every odd cycle of order at least three

Write $p=4m\pm1$ and $n=m-1$. Primality is unnecessary for the construction. Put $\theta=4\pi/p$, $\omega=e^{2i\theta}$ and $Q(X)=\prod_{j=1}^{n}(1-\omega^j X)$. Write $a_j$ for its coefficient of $X^j$. The identity
\[
 (1-\omega X)Q(\omega X)=(1-\omega^{n+1}X)Q(X)
\]
shows that successive coefficients have phase increment $\delta=m\theta-\pi=\pm\pi/p$ and positive radial ratio $\sin((m-j)\theta)/\sin(j\theta)$ for $1\le j\le n$. Since $n|\delta|<\pi/2$, all weights $\operatorname{Re}(a_j\overline{a_k})$ are positive. Place each at $4(j+k)\bmod p$. Their Fourier moments at frequencies $1,\ldots,n$ vanish by the roots of $Q$ and its coefficientwise conjugate. The product is a finite $q$-binomial product. The Lean proof derives the needed coefficient recurrence directly. [Positive quadrature proof](Green33RealQuadrature.lean) · [Finite $q$-binomial theorem, DLMF 17.2.35](https://dlmf.nist.gov/17.2.E35)

Because $4m\equiv\pm1\pmod p$, the occupied sites avoid $n$ disjoint pairs of cyclic neighbours. At $p=4m+1$ take the pairs starting at $4j+1$, and at $p=4m-1$ take those starting at $4j+2$, for $0\le j<n$. For a pair starting at $a$, let $y$ be the least nonnegative residue of $x-a$ and use the factor
\[
 2\sin(\pi y/p)\sin(\pi(y-1)/p).
\]
It vanishes at the pair and is positive elsewhere. It is also a constant minus a first-harmonic cosine. The product over all pairs has Fourier frequencies between $-n$ and $n$. Convolution with the first law kills every nonzero mode of this product. Normalizing gives two probability laws on the same $p-2n$ available sites with each sum probability exactly $1/p$. [Gap and constant-convolution proofs](Green33RealQuadrature.lean) · [Probability-law construction](Green33RealBudget.lean)

## Why the construction is sharp at primes three modulo four

The Biró–Tao prime uncertainty inequality gives $|\mathrm{supp}(f)|+|\mathrm{supp}(\widehat f)|\ge p+1$ for every nonzero complex input. The Lean proof derives it from the notebook's zero-convolution bound using a polynomial with a root at each occupied frequency. For a real probability law the spectral support is odd in size: zero is occupied and the remaining frequencies occur in conjugate pairs. For two laws with uniform sum, the two spectra intersect only at zero, so their sizes add to at most $p+1$. [Prime uncertainty principle](https://arxiv.org/abs/math/0308286) · [Notebook support inequality](PRIME-QUOTIENT-FLATNESS.md) · [Parity and minimum proof](Green33RealBudget.lean)

If $p=4m-1$ and both laws had at most $2m$ labels, both spectra would have at least $2m$ frequencies. Oddness raises each lower bound to $2m+1$, contradicting the total budget of $4m$. The construction uses $2m+1$. This proves the exact minimum on this class.

Sherstnev gives uniformity criteria for sums on finite abelian groups, and Peherstorfer treats positive quadrature exact for trigonometric polynomials on the circle. The support budget here couples a cancelling quadrature with a second law supported on the same labels. Duplicate checks covered the DeepMind statement issue and formalization PR, Left to Solve, Open Math Agents and the earlier notebook bounds. [Sherstnev](https://epubs.siam.org/doi/10.1137/S0040585X97976957) · [Peherstorfer](https://arxiv.org/abs/1001.2451) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Formalization PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents/issues?q=%22Green33%22)

Replay **Green33RealBudget** with the [notebook runner](../../scripts/replay-research). Eight notebook modules received independent Lean 4.33.1 kernel checks. The 56 axiom reports use only subsets of the standard three axioms.
