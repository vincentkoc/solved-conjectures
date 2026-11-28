# Affine flats in doubles of binary quadratic images

For \(x\in\mathbb F_2^n\), let \(h(x)=(1,x)\) and \(Q(x)=h(x)h(x)^{\mathsf T}\). For every subset \(B\subseteq\mathbb F_2^n\) and every \(d\ge3\),
\[
 Q(B)+Q(B)\text{ contains an affine }d\text{-flat}
 \quad\Longleftrightarrow\quad
 B\text{ contains an affine }(d+1)\text{-flat}.
\]
The cutoff is sharp. The quadratic double of the binary plane contains a linear plane, and the input has dimension two. [Inverse theorem and boundary example](Green51QuadraticSubset.lean)

For the full cube with \(n\ge4\), the largest flats in the double have dimension \(n-1\). There are exactly \(2^n-1\) of them. They are disjoint and indexed by the nonzero input differences \(t\). In particular the quadratic image of the four-dimensional cube has sixteen labels and its double has exactly fifteen affine three-spaces. [Fiber classification and count](Green51QuadraticFlats.lean)

## Recovering the input difference

Four or six distinct labels cannot sum to zero. For a zero relation on \(k\) distinct labels, place the corresponding columns \(h(x)\) in a matrix \(M\). Then \(MM^{\mathsf T}=0\), so its rank is at most \(k/2\). The columns and their translates by any one column form two disjoint sets of size \(k\) in the column space, distinguished by the leading coordinate. This gives \(2k\le 2^{\lfloor k/2\rfloor}\). At \(k=8\) the columns fill the entire leading-one slice of a four-dimensional space. The eight input points therefore form an affine three-space. This is also the minimum-weight support property of the corresponding binary Reed–Muller code. [Lean rank proof](Green51QuadraticRelations.lean) · [Leducq’s proof of the Delsarte–Goethals–MacWilliams theorem](https://doi.org/10.1016/j.ffa.2011.12.003)

Choose a pair of labels representing each point of an affine three-space in the double. The sixteen endpoints are distinct by the affine matching bound. Over each four-point plane of the three-space, the eight endpoints give a zero relation, so their input points form an affine three-space. Two index planes meeting in a line give two input flats meeting in exactly four points. Those four form a plane. Hence the two input pairs on that line have the same difference. Every line gives this equality, forcing one common \(t\) throughout the represented flat. Restriction to three-spaces gives the same conclusion in every higher dimension. [Affine matching bound](AFFINE-FLAT-MATCHINGS.md)

For fixed \(t\ne0\), the map \(x\mapsto Q(x)+Q(x+t)\) is affine with linear kernel \(\langle t\rangle\). Its image is the entire fiber of the double with first row \((0,t)\). Each point has just the two input preimages \(x,x+t\). Pulling a represented \(d\)-flat back through this map therefore gives a \((d+1)\)-flat inside \(B\). Conversely, on any \((d+1)\)-flat inside \(B\), choosing a nonzero direction \(t\) and applying the same map gives a \(d\)-flat in the double.

These are flats in the sum of two points of the displayed binary image. De Seguins Pazzis classifies maximal-dimensional affine spaces in the larger ambient collection of bounded-rank symmetric matrices. [Bounded-rank matrix spaces](https://arxiv.org/abs/1507.06213) · [Pinned Green 51 question](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)
