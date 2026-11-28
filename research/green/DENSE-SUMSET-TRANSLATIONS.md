# Which translates are dense sumsets?

In the labelled binary cube of dimension 16, consider the sumsets $S=A+A$ with $|A|>25{,}376$, exactly 41 missing points, and largest affine subspace of dimension 14. Every such $S$ has precisely four translates that admit a generating set above the same density. All four are distinct and have largest affine dimension 14. Grouping the sumsets by translation gives exactly

$$
7\,173\,767\,398\,331\,178\,268\,151\,749\,942\,350\,710\,292\,430\,047\,640\,794\,411\,461\,865\,652\,617\,216\,000
$$

classes. Here the equivalence relation allows every translation of the ambient cube. The four are the representatives of a class that meet the stated conditions. [Count up to translation](Green51DenseTranslationCount.lean) · [Labelled count](DENSE-SUMSET-ENUMERATION.md)

Write $n=2(s+1)+r$, $g=2s+3$ and $\ell=2^r$, with $s\ge5$. Take any $S=A+A$ in $\mathbb F_2^n$ whose largest affine subspace has dimension $n-2$ and whose generating set has density greater than $\tfrac12-\binom{2s}{s}/2^{2s+1}$. Put $D=S^c$ and $k=|D|$. Whenever $8k>\ell\min(5g+12,4g+20)$, the following three conditions on $b$ are equivalent.

- $S+b$ admits a generating set above the same density.
- $b$ belongs to a fixed subspace $P$ of order $\ell$.
- $|D\cap(D+b)|>2\ell$.

The third condition determines $P$ from the missing points alone. For odd $k$ the number of translation classes is the labelled count divided by $\ell$. Summing the points of an odd set distinguishes its translates, since translating by $b$ adds $b$ to that sum. At even $k$ the subspace still gives exactly the allowed shifts, and distinct shifts can give the same set. [Recovering the subspace](Green51FrameAutocorrelation.lean) · [Translation classes](Green51TranslationClasses.lean)

To prove the test, place $D$ in its odd-circuit frame $U=P+C$. If $b\in P$, then $D$ and $D+b$ both lie in $U$, so their intersection has at least $2k-g\ell>2\ell$ points. If $b\notin P$, a nonzero translate of the quotient circuit meets it in at most two labels. Each label accounts for at most $\ell$ points. This intersection count is invariant under translating $D$. Any dense realization after a shift must therefore have the same frame period $P$. [Circuit intersection](Green51CircuitOverlap.lean) · [Shift criterion](Green51RealizableShifts.lean)

Modulo $P$, the missing points occupy exactly the $g$ circuit labels, whose sum is zero. Translation changes their sum by the class of $b$, because $g$ is odd. A second dense realization forces this class to be zero. Conversely, a shift in $P$ keeps the missing points inside the original frame, where the earlier realization theorem applies. Geelen's sharp odd-girth bound and Alon–Zamir's count of unrestricted binary sumsets provide the background. Green's general dimension question remains open. [Quotient labels](Green51QuotientOrigin.lean) · [Realization](PRESCRIBED-MISSING-DIRECTIONS.md) · [Geelen](https://arxiv.org/abs/1401.5769) · [Alon–Zamir](https://arxiv.org/abs/2403.16589)

From the pinned Formal Conjectures checkout, replay the result with `lake env python3 "$runner" Green51DenseTranslationCount`, using the [notebook replay setup](../README.md#replay).
