# Repairing square-order planar seeds in the cyclic double

Put \(q=t^2\), \(h=q+t+1\), \(j=q-t+1\) and \(v=hj=q^2+q+1\). Let \(D\) be a planar difference set of size \(q+1\) in \(\mathbb Z/v\mathbb Z\), with exactly one ordered representation of each nonzero difference. The old odd layer \(B\) may contain up to \(q+1\) elements. Write \(R=2D\cup(1+2B)\subseteq\mathbb Z/(2v)\mathbb Z\). For a full ordinary two-basis \(T\), count the fresh labels by \(w=|T\setminus R|\). Old labels may be discarded.

| Location of \(B\), as \(t\to\infty\) | Lower bound on \(\liminf w/q\) | Lower bound on \(\liminf |T|/\sqrt{2v}\) when \(R\subseteq T\) and \(|B|=q+1\) |
| --- | --- | --- |
| One coset of the subgroup of order \(h\) | \((\sqrt5-1)/2\) | \((3+\sqrt5)/(2\sqrt2)\) |
| \(o(t)\) such cosets | \(\sqrt2-1\) | \(1+1/\sqrt2\) |

Each Lean statement gives eventual strict inequality for every coefficient below the displayed number. For a balanced one-coset seed the previous exact coverage formula gives a weaker completion coefficient of \(\sqrt{5/2}\) by counting all fresh pairs. Counting the even residues separately gives the first row. Green 33 quantifies over unrestricted full bases. [Cyclic bounds](Green33BaerParity.lean) · [Finite coverage and attribution](BAER-COSET-COVERAGE.md) · [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

## The finite inequality

Use the Chinese remainder coordinates of orders \(h,j\). Let \(P\subseteq\mathbb Z/j\mathbb Z\) contain the second coordinates of \(B\) after translating the seed by its planar centroid. Set \(L=q+t\). Split the fresh labels into \(x\) even labels and \(y\) odd labels. Then \(x+y=w\) and
\[
2v\ \le\ (q+1)(q+2)+|P+P|L+x(q+1)
 +\min\{2|B|y,\,|P|yL\}+x^2+x+y^2+y .
\]
The original even sums from \(D+D\) fill the central row. Every other row has just \((h-1)/2\) holes. Thus each row supporting \(1+B+B\) can supply at most \(L/2\) fresh residues. One new odd point paired with \(B\) can use at most \(|P|\) rows and at most \(|B|\) sums. For the new even points paired with \(D\), perfect difference coverage and the Sidon property give at most \(x(q+1)/2\) fresh sums. Finally, pairs of two new labels can produce even residues only within the same parity. Their two unordered-pair budgets give \(x(x+1)/2+y(y+1)/2\). [Weighted row profile](Green33BaerLayers.lean) · [Sidon fresh-sum bound](Green33SidonLayerRepairs.lean) · [Finite certificate](Green33BaerParity.lean)

If \(|P+P|/q\to\rho\), every nonnegative \(s\) with \(\rho+2s+s^2<1\) satisfies \(w>sq\) eventually. One occupied coset improves the linear term to \(s\) and gives \(\rho=0\). For \(|P|=o(t)\), the inequality \(|P+P|\le |P|^2=o(q)\) gives the second row. When \(T\) retains a balanced seed it contains \(2(q+1)+w\) labels. This yields the stated coefficients in the actual cyclic double. [Asymptotic theorems](Green33BaerParity.lean)

## Verification

A direct Lean comparison uses the pinned Green 33 quantifiers, its positive modulus and ordinary pointwise sumset. It proves that a full superset of a balanced one-coset seed eventually fails the literal tolerance \(\varepsilon=1/4\). At \(q=4\), a deterministic sample of replacement sets in \(\mathbb Z/42\mathbb Z\) contained 2,579 full bases that deleted old labels. Every one satisfied the finite parity inequality.

Lean 4.33.1 rebuilt the 27-module import closure. Each module passed an independent kernel replay, and all 193 printed declarations use only `propext`, `Classical.choice` and `Quot.sound`. The classical structure of the Baer sub-difference set and its noncentral rows is described in the proof of Jungnickel’s Theorem 6.1. [Jungnickel, §6](https://doi.org/10.4153/CJM-1987-051-1) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613)
