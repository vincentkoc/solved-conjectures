# Three-space counts at the sixteen-label threshold

Let \(A\) have sixteen points in a finite binary vector space. Suppose its double \(A+A\) contains an affine three-space and no linear three-space. Count distinct affine three-spaces by their point sets. The affine dimension of \(A\) determines the count.

| Affine dimension of \(A\) | Three-spaces in \(A+A\) | Incidence |
| --- | --- | --- |
| 11 | 1 | Its eight points are the eight distinguished pair sums of the universal model. |
| 10 | 15 | Every nonzero pair sum belongs to exactly one of the fifteen spaces. |

Both rows occur. The theorems `exact_count` and `unique_through_nonzero` apply to the original set in any finite binary ambient space. [Lean proof](Green51WitnessIncidence.lean) · [Two affine types](SIXTEEN-LABEL-TYPES.md)

## How a hyperplane restricts the pairs

Suppose \(p+W\subseteq A+A\), where \(\dim W=d\ge3\), and the double avoids linear three-spaces. Choose a pair of labels for each point of \(p+W\). All \(2^{d+1}\) endpoints are distinct. If a linear functional \(f\) takes the value one somewhere on the flat, it takes that value on at least half its points. Each of their pairs uses one label in each level of \(f\). Thus each input level contains at least \(2^{d-1}\) labels. The theorem `hyperplane_cost` works for arbitrary \(A\) and \(d\). [Disjoint representatives](Green51QuadraticFlats.lean)

In the universal paired model, a horizontal coordinate is one at only two labels. Since \(2^{d-1}\ge4\), every represented flat of rank at least three has every horizontal coordinate zero. The nonzero sums with zero horizontal part are exactly the original vertical pair sums. A represented flat of rank at least three excludes zero, since otherwise it would contain a linear three-space. For eight original pairs this leaves precisely one flat. The same argument confines all higher-rank flats of every universal paired model to its distinguished vertical flat.

For the ten-dimensional type, the quadratic image of the four-dimensional cube supplies a witness with fifteen disjoint affine three-spaces. This realizes the smaller type by the two-type classification and the uniqueness just proved for the larger type. The nonzero first row of a pair sum specifies its unique space. Counting carriers and incidence commutes with translations of the labels and injective linear embeddings. [Quadratic fibers](QUADRATIC-IMAGE-FLATS.md) · [Pinned Green 51 statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)
