# The sharp local dimension for affine flats in binary sumsets

Let \(A\) be a subset of a finite vector space over \(\mathbb F_2\). If \(p+W\subseteq A+A\) with \(\dim W=d\), some \(B\subseteq A\) already represents the entire prescribed flat and satisfies
\[
 |B|\le 2^{d+1},\qquad \dim\operatorname{aff}(B)\le 2^d+d .
\]
For every \(d\ge3\), both upper bounds are sharp in the same example, even when \(B+B\) may represent any affine \(d\)-flat. For \(d=3\) the optimal universal budgets are sixteen labels and eleven affine dimensions. There also exist sixteen-label witnesses in ten dimensions. [Proof](Green51LocalFlats.lean) · [The ten-dimensional example](DIMENSION-TEN.md)

The theorem `guaranteed_iff` expresses \(d\le F(n,\alpha)\), for \(d>0\) and \(\alpha\le1\), in the original Green 51 predicate. Every set at the requested density must contain one of these bounded witnesses. The budgets depend only on the target rank. [Pinned definition](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

## Choosing the labels

For each \(w\in W\), choose \(x_w,y_w\in A\) with \(x_w+y_w=p+w\). After translation by \(x_0\), all chosen labels lie in the span of \(W\), \(p\), and the \(2^d-1\) differences \(x_w+x_0\) with \(w\ne0\). This gives the dimension bound and retains every original pair sum.

## An example attaining both bounds

Index independent coordinate vectors \(e_z\) by \(z\in\mathbb F_2^d\). Take the two labels \((e_z,0,0)\) and \((e_z,1,z)\) at each index. Their sums contain the flat \((0,1,z)\). In any zero relation, the coordinate vectors force whole pairs to be selected. The flag requires an even number of pairs, and two different indices cannot sum to zero. Hence there are no four- or six-label relations and the double avoids every linear three-space. The sixteen-label argument in rank three extends to a cost of \(2^{d+1}\) labels for any affine \(d\)-flat when \(d\ge3\). Any representing subset therefore equals the whole example. [Four- and six-label criterion](SPARSE-THREE-SPACES.md) · [Rank-dependent cost](AFFINE-FLAT-MATCHINGS.md)

The labels span a linear space of dimension \(2^d+d+1\). The left labels supply all independent coordinate vectors. Pair sums give the flag and all \(d\) remaining directions. A translate of a subspace of dimension \(r\) has linear span of dimension at most \(r+1\), so the labels need at least \(2^d+d\) affine dimensions.
