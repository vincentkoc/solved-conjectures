# What every extremal 24-label double contains

In \(\mathbb F_2^{11}\), let \(A\) have 24 points and suppose \(A+A\) avoids every linear three-space. Then \(A+A\) contains **exactly 11,385 affine three-spaces**. Each nonzero point of \(A+A\) belongs to **exactly 330** of them. The explicit extended Golay witness attains these counts. Twenty-four is the maximum possible number of labels under the avoidance hypothesis. [Flat counts](Green51ExtremalFlatCounts.lean) · [Sharp thresholds and witnesses](ELEVEN-DIMENSION-THRESHOLDS.md) · [Pinned Green 51](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

## The zero-sum octads

All single-label and three-label sums are distinct under linear avoidance. At 24 labels their number is \(24+\binom{24}{3}=2048\), so every ambient point has a unique such representation. Apply this to the sum of five specified labels. A singleton or an intersecting triple would give a zero sum on two, four or six labels. The unique representation is therefore a disjoint triple. Together the eight labels form an octad, and it is the only zero-sum octad containing the five specified labels. [Perfect packing and octads](Green51PerfectPacking.lean)

Thus the zero-sum octads of each extremal set form a Steiner system \(S(5,8,24)\). Counting extensions of a specified \(i\)-subset to five labels gives the following incidence numbers. The Golay code and the Witt design are classical. Curtis describes their connection and the octad geometry. [Curtis on the binary Golay code](https://www.lms.ac.uk/sites/default/files/4.%20Curtis%20-%20Error%20Correction%20and%20the%20Binary-Golay%20Code.pdf) · [Curtis on the Steiner system](https://doi.org/10.1017/S0305004100052075)

| Number of specified labels | 0 | 1 | 2 | 3 | 4 | 5 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Octads containing them | 759 | 253 | 77 | 21 | 5 | 1 |

Distinct octads meet in at most four labels. To see that they meet evenly, fix an octad \(O\). The expression
\[
g(r)=r-2\binom r2+4\binom r3-8\binom r4
\]
is the parity indicator for \(0\le r\le4\). The incidence numbers give \(\sum_U g(|O\cap U|)=-384=g(8)\). The term \(U=O\) accounts for the entire sum. For any nonempty even zero-sum subset, choosing five of its labels and taking the symmetric difference with their octad shortens the subset. Induction shows that every even zero-sum subset meets every octad evenly. [Intersection moments](Green51OctadParity.lean) · [Descent by octads](Green51OctadSlices.lean)

## From octads to affine three-spaces

Each label lies in 253 octads, so summing all zero-sum octads gives \(\sum A=0\). The sixteen-label zero-sum subsets are exactly the complements of octads. Each complement lies in an affine hyperplane. Otherwise its augmented columns would span the full space, producing an even relation meeting the omitted octad in one label. The sixteen-label classification now gives exactly fifteen affine three-spaces in the double of each complement, with each nonzero local pair sum on one of those flats. [Complement geometry](Green51OctadFlats.lean) · [Sixteen-label classification](THREE-SPACE-COUNTS.md)

Every affine three-space in \(A+A\) has a sixteen-label zero-sum witness retaining that very flat. Its witness is unique. Two different sixteen-label subsets share fewer than sixteen labels, and the uniqueness of every nonzero pair representation would place a shared flat in the double of their intersection. That would violate the sixteen-label minimum. The 759 complements therefore contribute \(759\cdot15=11{,}385\) distinct flats. For a pair of labels, exactly \(759-2\cdot253+77=330\) octads avoid both. Each of those complements contributes one flat through the pair sum. [Disjoint family count and point incidence](Green51ExtremalFlatCounts.lean)

From the pinned Formal Conjectures checkout, set `notebook` to this repository’s path and run `lake env python3 "$notebook/scripts/replay-research" Green51ExtremalFlatCounts`.
