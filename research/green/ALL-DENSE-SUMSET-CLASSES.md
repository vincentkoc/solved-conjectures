# Translation classes of all dense binary sumsets

In $\mathbb F_2^{16}$, consider every sumset $S=A+A$ with $|A|>25{,}376$. With 41 missing points, there are about $7.9281\times10^{135}$ translation classes. With 58 missing points, there are about $6.3684\times10^{183}$. A class counts once if at least one translate has such a generator. These counts include every possible largest affine dimension of $S$. The [two exact integers](Green51AllClassExamples.lean) specialize the [general formula](Green51AllDenseTranslationClasses.lean).

For $s\ge5$ and $r\ge0$, put $n=2(s+1)+r$, $g=2s+3$, $\ell=2^r$, and $\alpha=\tfrac12-\binom{2s}{s}/2^{2s+1}$. Take $\ell\min(5g+12,4g+20)<8k\le8g\ell$. Let $N(n,k,\alpha)$ count labelled outputs with $k$ missing points, a generator of density greater than $\alpha$, and largest affine dimension $n-2$. Write $F(n,k)$ for the number of $k$-subsets of proper affine span. The complete class count is

$$
\frac{F(n,k)+(2^n-1)\mathbf1_{2\mid k}F(n-1,\lfloor k/2\rfloor)}{2^n}
+
\frac{N(n,k,\alpha)+(2^n-1)\mathbf1_{2\mid k}N(n-1,\lfloor k/2\rfloor,\alpha)}{2^r}.
$$

The first term counts all orbits of nonspanning missing sets. For a missing set $D$ of affine rank $d<n$, the complement of $D+b$ has a dense generator exactly when $b$ is outside the affine span of $D$. This gives $2^n-2^d$ eligible shifts. A nonzero period fixes precisely the masks pulled back from a quotient of dimension $n-1$, which accounts for the even correction. In the second term the earlier circuit classification gives $2^r$ eligible shifts. Every missing set in those classes spans the whole affine space. [Origin criterion](Green51AffineTranslationOrigins.lean) · [Quotient count](Green51AffineOrbitCount.lean) · [Circuit periods](DENSE-SUMSET-PERIODS.md)

The affine term can be computed with integer arithmetic. Let $B_{k,d}$ count the $k$-point subsets of affine rank $d$ in dimension $n$. For $k=1$, only $B_{1,0}=2^n$ is nonzero. Adding one marked point gives

$$
(k+1) B_{k+1,d}=(2^d-k) B_{k,d}+(2^n-2^{d-1})B_{k,d-1},
$$

with the second term omitted at $d=0$. An insertion preserves the rank inside the affine span and raises it by one outside. Consequently $F(n,k)=\binom{2^n}{k}-B_{k,n}$ for $k>0$. [Insertion count](Green51AffineRankCounts.lean) · [Integer recurrence](Green51AffineRankNumbers.lean)

The orbit calculation uses the classical Cauchy–Frobenius formula. Green and Ruzsa studied counting sumsets in cyclic groups, and Alon and Zamir studied the asymptotic number of binary sumsets. The input on binary odd circuits builds on Geelen. Green's general question asks for the largest affine dimension guaranteed at each density and dimension. That function remains open. [Green–Ruzsa](https://people.maths.ox.ac.uk/greenbj/papers/sumsets-sumfreesets.pdf) · [Alon–Zamir](https://arxiv.org/abs/2403.16589) · [Geelen](https://arxiv.org/abs/1401.5769) · [Pinned problem](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

From the pinned Formal Conjectures checkout, run `lake env python3 "$runner" Green51AllClassExamples` using the [notebook replay setup](../README.md#replay).
