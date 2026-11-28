# Exact dimension below the hyperplane threshold

Write $F(n,\alpha)$ for the largest affine dimension guaranteed in $A+A$ for every $A\subseteq\mathbb F_2^n$ of density at least $\alpha$. For every fixed $0<c<1$ and all sufficiently large $n$,
$$
 F\!\left(n,\frac12-\frac{1}{\sqrt{2\pi(n-c\log_2 n)}}\right)=n-2.
$$
A linear subspace of codimension at most two works for every admissible set. A Hamming ball gives the matching upper bound even for affine subspaces. At the unshifted density the exact dimension is $n-2$ in even dimensions and $n-1$ in odd dimensions. [Logarithmic shift](Green51ShiftedCriticalDensity.lean) · [Unshifted critical density](CRITICAL-DENSITY.md) · [Pinned Green 51](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

## Finite density intervals

Put $h_m=\tfrac12-\binom{2j}{j}/(2\cdot4^j)$, where $j=\lfloor m/2\rfloor$. For $n\ge16$, let $k=\lfloor\log_2 n\rfloor$ and $d=k-\lfloor\log_2(k+2)\rfloor$. The equality $F(n,\alpha)=n-2$ holds throughout $h_{n-d-1}<\alpha\le h_n$. The proof also gives a finite test. For any $s,d\ge0$ with $2\le n\le 2(s+1)+d$ and $2^d(d+2)+4\le 4(s+1)$, the equality holds for $h_{2s}<\alpha\le h_n$. The lower endpoint is strict. The full range of densities with this answer remains open. [Finite interval and logarithmic bound](Green51LogDensityWindow.lean)

| Ambient dimension | Minimum size of $A$, inclusive | Guaranteed affine dimension |
| --- | --- | --- |
| 12 | 1,489 through 1,586 | 10 |
| 16 | 25,377 through 26,333 | 14 |

## Missing directions

Let $D$ be the complement of $A+A$. Folded-cube averaging converts the density lower bound into a lower bound $g$ on the size of every odd zero-sum subset of $D$. If one binary linear functional takes the value one throughout $D$, its kernel already lies in $A+A$. Otherwise choose a shortest odd circuit $C$, delete one point and extend the remaining independent family to a basis of the span of $D$ using elements of $D$. There are at most $d$ additional basis elements when the ambient rank is at most $g-1+d$. [Folded-cube bound](Green51MissingDirections.lean) · [Circuit coordinates](Green51OddCircuitBasis.lean)

Each missing direction has a representation using $S\subseteq C$ and a subset $Q$ of the additional basis elements, with $|S|+|Q|$ odd. The complement of $S$ in $C$ represents the same circuit sum. Minimality of $C$ implies $|S|\le |Q|+1$. Two representations with the same $Q$ have circuit parts at Hamming distance at most two. Choose a largest circuit part in each nonempty slice. Every member of the slice has at most one coordinate outside that representative. With $e\le d$ additional basis elements, the representatives occupy at most $\sum_Q(|Q|+1)=2^e(e+2)/2$ coordinates altogether. [Slice estimates](Green51OddCircuitSlices.lean)

The finite test leaves two basis coordinates outside all those representatives. No odd representation uses both. For each marked coordinate take a binary functional that is one on every other circuit coordinate and on the additional basis elements. At least one of the two functionals is one on each missing direction, so their common kernel lies in $A+A$. [Linear four-colouring](Green51GirthColouring.lean)

Sanders studied the near-half density regime. Kohlmeyer and Kruer proved that codimension stays bounded for each fixed coefficient of $1/\sqrt n$, and Faldor formalized that result. Beaudou, Naserasr and Tardif proved the projective-cube subgraph theorem for binary Cayley graphs of prescribed odd girth. The exact function in Green 51 is still open outside known ranges. [Sanders](https://arxiv.org/abs/1003.5649) · [Kohlmeyer and Kruer](https://liamkruer.com/assets/work/conjectures/problems/green-51/paper/proof.pdf) · [Faldor’s formalization](https://github.com/lefttosolve2/open-math-agents/pull/5448) · [Beaudou, Naserasr and Tardif, Theorem 1.5](https://www.irif.fr/~reza/pdfs/papers/BNT15.pdf)

Replay from the pinned Formal Conjectures checkout with `lake env python3 /path/to/solved-conjectures/scripts/replay-research Green51ShiftedCriticalDensity`.
