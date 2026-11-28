# The first guaranteed three-space in dimensions three through nine

Write \(F(n,\alpha)\) for Green's guaranteed affine dimension in \(A+A\). For \(3\le n\le9\) and \(\alpha\le1\), the exact threshold is
\[
F(n,\alpha)\ge3 \quad\Longleftrightarrow\quad \alpha>M(n)/2^n.
\]
The upper endpoint belongs to the lower plateau: \(F(n,\alpha)=2\) when \(2<\alpha\,2^n\le M(n)\). The same \(M(n)\) is the maximum number of points whose double can avoid a **linear** three-space. [Pinned Green 51](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean) · [Threshold and witnesses](Green51SmallWitnesses.lean)

| Dimension \(n\) | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Largest avoiding size \(M(n)\) | 4 | 5 | 6 | 8 | 9 | 10 | 12 |
| First forcing size | 5 | 6 | 7 | 9 | 10 | 11 | 13 |

## The upper bound

If \(k\ge5\) labels avoid a linear three-space in their double, the check matrix with columns \((1,a)\) has an even binary kernel of dimension \(h\ge k-n-1\) and minimum nonzero weight at least eight. Summing weights by coordinates gives the linear Plotkin inequality \(16(2^h-1)\le k\,2^h\). In particular \((16-k)2^{\max(k-n-1,0)}\le16\) when \(k\le16\). Substituting the first forcing size in each column rules it out, and a larger set contains a subset of that size. [Plotkin, *Binary codes with specified minimum distance* (1960)](https://doi.org/10.1109/TIT.1960.1057584) · [Checked bound](Green51SmallDimensions.lean) · [Four- and six-label criterion](SPARSE-THREE-SPACES.md)

## Witnesses at equality

Start with zero and the \(n\) coordinate vectors. In dimensions six through nine, add the vector supported on the first six coordinates. In dimension nine, also add the vector supported on the last six. Every nonempty sum of the extra vectors has weight six, including the sum of the two in dimension nine. A relation on at most six distinct labels using an extra vector has at most five remaining coordinate vectors to cancel it. Distinct coordinate vectors are independent, and adjoining zero creates no four- or six-label relation. Thus the doubles avoid a linear three-space. An affine three-space in any such double would require at least sixteen labels. [Witness proof](Green51SmallWitnesses.lean) · [Sixteen-label minimum](AFFINE-FLAT-MATCHINGS.md)
