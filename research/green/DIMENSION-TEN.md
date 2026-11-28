# Affine and linear three-spaces first separate in dimension ten

In \(\mathbb F_2^{10}\), sixteen points always force an affine three-space in \(A+A\). Seventeen points force a linear three-space. Both numbers are sharp. In dimensions three through nine the two thresholds coincide. [Threshold proofs](Green51FirstSeparation.lean) · [Earlier dimensions](FIRST-THREE-SPACE.md)

For the pinned function \(F(10,\alpha)\), the exact first threshold is
\[
F(10,\alpha)\ge3\quad\Longleftrightarrow\quad 1024\alpha>15
\qquad(\alpha\le1).
\]
The value is two on \(2<1024\alpha\le15\) and three on \(15<1024\alpha\le16\). At the sixteen-point boundary a linear three-space can still be absent. In every such extremal example, **each nonzero point of the double lies on an affine three-space contained in the double**. [Pinned Green 51](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean) · [Sixteen-point example](AFFINE-FLAT-MATCHINGS.md)

## Why the thresholds differ

If a sixteen-point set avoids a linear three-space in its double, the columns \((1,a)\) give a binary kernel \(C\) of dimension at least five and minimum nonzero weight at least eight. These are the parameters of the classical first-order Reed–Muller code. The proof uses two consequences of equality in the Plotkin bound. The kernel contains the all-ones word, and every other nonzero word is balanced. They follow by summing the imbalance \(16-2\operatorname{wt}(x)\) and its square over \(C\). The all-ones word says that the sixteen labels sum to zero. Applying this conclusion to every deletion from a hypothetical seventeen-point avoiding set would make all seventeen labels equal. [Chen and Vinck, Theorem 2.1](https://arxiv.org/abs/0901.2062) · [Binary moment proof](Green51Hadamard.lean)

Fix two distinct labels. The kernel words that vanish at both positions form a subspace of dimension at least three. Choose three independent rows there. Every nonzero combination is balanced, so each of the eight column patterns occurs twice. The chosen labels form the pair with pattern zero. Summing the two labels in each pair gives eight distinct points in \(A+A\). For every plane through zero among the eight patterns, the indicator of its preimage is a kernel word. The eight pair sums therefore preserve parallelograms and form an affine three-space through the prescribed sum. [Pair partition and affine embedding](Green51FirstSeparation.lean)
