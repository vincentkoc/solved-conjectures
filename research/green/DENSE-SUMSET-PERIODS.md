# Periods of dense binary sumsets

In dimension 16, let $S=A+A$ with $|A|>25{,}376$, exactly 58 missing points, and largest affine subspace of dimension 14. The exact number of translation classes meeting these conditions is

$$
7\,382\,900\,503\,403\,380\,984\,596\,214\,809\,995\,558\,666\,997\,109\,553\,143\,952\,179\,200
$$

The allowed shifts form a space of order four. In each circuit frame, the missing set occupies 58 of 60 positions arranged in fifteen four-point cosets. The two unused positions lie in distinct cosets in 1,680 cases, giving 420 classes of size four. They lie in the same coset in 90 cases, giving 45 classes of size two. [Lean example](Green51EvenMissingExample.lean) · [Circuit-frame enumeration](DENSE-SUMSET-ENUMERATION.md)

Write $N(n,k,\alpha)$ for the number of labelled $S=A+A$ in $\mathbb F_2^n$ with $|S^c|=k$, largest affine dimension $n-2$, and some generator of density greater than $\alpha$. For a prescribed $h$-dimensional subspace $H$, the count of such $S$ fixed by every shift in $H$ is zero unless $2^h\mid k$. When $2^h\mid k$, it equals $N(n-h,k/2^h,\alpha)$, provided $n-h\ge3$. Indeed, a set fixed by $H$ is the full preimage of its quotient. Pullback raises the largest affine dimension of a nonempty set by $h$. A quotient generator lifts at the same density, and the image of an upstairs generator has at least its density. [Quotient count](Green51FixedKernelCount.lean) · [Affine dimension](Green51QuotientFlatDimension.lean)

Now take $s\ge5$, $n=2(s+1)+r$, $g=2s+3$, $\alpha=\tfrac12-\binom{2s}{s}/2^{2s+1}$ and $8k>2^r\min(5g+12,4g+20)$. Each counted set then has $2^r$ allowed shifts. If $T(n,k,\alpha)$ counts translation classes meeting the family, the exact formula is

$$
2^r T(n,k,\alpha)
 = N(n,k,\alpha) + (2^n-1)\,\mathbf 1_{2\mid k}\,N(n-1,\lfloor k/2\rfloor,\alpha).
$$

The family can occupy just part of a translation orbit. Each representative contributes its stabilizer order to the fixed-point sum. Within a class these orders sum to $2^r$. The zero shift fixes every set, and each nonzero shift has the one-dimensional quotient count above. This is the Cauchy–Frobenius counting argument applied to the admissible shifts. [Translation formula](Green51PeriodClassCount.lean) · [Restricted orbit count](Green51RestrictedOrbitCount.lean) · [Allowed shifts](DENSE-SUMSET-TRANSLATIONS.md)

The period space of $S$ consists of the shifts fixing $S$. In the stated window its dimension $d$ is at most $r$, its order $2^d$ divides $k$, and its class has $2^{r-d}$ representatives. Write $a_d$ for the number of labelled sets of period dimension $d$. The Gaussian binomial coefficient counts subspaces of a given dimension. Counting a set together with an $h$-dimensional subspace of its periods gives, for $0\le h\le r$,

$$
\sum_{d=h}^{r}{d\brack h}_2\,a_d
= {n\brack h}_2\,\mathbf 1_{2^h\mid k}\,N(n-h,\lfloor k/2^h\rfloor,\alpha).
$$

The diagonal coefficient is one, so descending from $h=r$ determines every $a_d$. The fixed-subspace counts and the incidence identity also hold at arbitrary density thresholds when the quotient dimension is at least three. Geelen provides the binary odd-girth background for the frame theorem. Alon and Zamir study the asymptotic number of unrestricted binary sumsets. Green's general affine-dimension question remains open. [Period spectrum](Green51PeriodSpectrum.lean) · [Subspace counts](Green51PeriodSubspaces.lean) · [Geelen](https://arxiv.org/abs/1401.5769) · [Alon–Zamir](https://arxiv.org/abs/2403.16589)

From the pinned Formal Conjectures checkout, run `lake env python3 "$runner" Green51PeriodSpectrum Green51EvenMissingExample` using the [notebook replay setup](../README.md#replay).
