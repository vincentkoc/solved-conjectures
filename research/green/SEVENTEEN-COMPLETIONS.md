# Completing seventeen labels in eleven binary dimensions

Let \(A\) be a set of 17 points in \(\mathbb F_2^{11}\) for which \(A+A\) contains no three-dimensional linear subspace. Two tests on the labels determine exactly how far \(A\) can be extended. A zero sum here uses distinct labels. Counts are of actual supersets of \(A\) in the given space. [Classification and existence of all three cases](Green51SeventeenSpectrum.lean)

| Zero sums in \(A\) | Choices for an eighteenth point | Completions to 24 points |
| --- | ---: | ---: |
| Ten labels sum to zero | 0 | 0 |
| Neither ten nor sixteen labels sum to zero | 13 | 2 |
| Sixteen labels sum to zero and no ten do | 28 | 8 |

For a maximal example, take zero, the eleven coordinate vectors, and the points with binary labels \(843,1365,1638,1927,2032\). The five extra points together with \(0,1,2,4,8\) sum to zero. An avoiding 18-point set cannot contain such a relation. The other two cases come from removing one point from the two examples at size 18, preserving a sixteen-point zero sum when one is present. [Maximal example and certificate](Green51SeventeenWitness.lean) · [Examples at size 18](Green51ShortenedFlatCounts.lean)

## Counting the extensions

The binary code of relations between the columns \((1,a)\), for \(a\in A\), has dimension five and minimum distance eight. In the order of the rows above, the numbers of words at weights \(8,10,12,16\) are \((22,8,0,1)\), \((25,0,6,0)\), and \((30,0,0,1)\). The proof restricts the code outside a word of weight ten or fourteen and uses the MacWilliams identities for the dual weights. In the two cases without a weight-ten word, the dual has 896 words of weight congruent to three modulo four. Of these, 15 and zero, respectively, have weight three. Dividing 896 by the 32 words in the relation code and subtracting the weight-three count gives 13 and 28 possible new labels. [Weight distributions](Green51SeventeenProfiles.lean) · [One-point extension count](Green51ExtensionFibres.lean)

Each 24-point completion uses seven new labels. Two distinct completions can share at most one of them because any 19 shared points determine a unique completion. In the 13-label case one completion cannot cover all choices and three would use at least 18 labels. In the 28-label case each eighteenth point lies in exactly two completions, since it preserves the sixteen-label relation. Counting incidences gives \(28\cdot2/7=8\). [Intersection argument](Green51SeventeenCompletions.lean) · [Completion theorem for 18–24 labels](SHORTENED-COMPLETIONS.md)

Bouyukliev, Bouyuklieva, Gulliver and Östergård record five equivalence classes of binary \([17,5,8]\) codes, two of them self-orthogonal. Dodunekov and Encheva classify the related codes of lengths 18 through 23 up to equivalence. The counts here keep the 17 labels fixed and distinguish each extension inside their ambient space. Green’s general question about affine subspaces remains open. [Length-17 classification, §10](https://combinatorialpress.com/article/jcmcc/Volume%20059/vol-059-paper%203.pdf) · [Dodunekov and Encheva](https://www.mathnet.ru/eng/ppi162) · [Pinned problem](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

From the pinned Formal Conjectures checkout, set `notebook` to this repository's path and run `lake env python3 "$notebook/scripts/replay-research" Green51SeventeenSpectrum`.
