# Unique completion at twenty-three labels

Let \(A\) be a 23-point subset of \(\mathbb F_2^{11}\) whose double \(A+A\) contains no linear three-space. There is a unique point that can be added while preserving this property. It is \(p=\sum_{a\in A}a\). The double of the original 23 points contains **3,795 affine three-spaces**, and each of its 253 nonzero points belongs to **120** of them. The seven-label subsets with sum \(p\) form a Steiner system \(S(4,7,23)\). [Completion theorem](Green51MissingLabel.lean) · [Incidence and heptads](Green51DeletedLabels.lean) · [Pinned Green 51](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

## Why the missing label works

Linear avoidance excludes zero sums of four and six distinct labels. For an even zero-sum subset of size \(n\), append a leading one to each column. The binary kernel \(C\) of these augmented columns contains the all-one word, has minimum distance at least eight and has size at least \(2^{n-12}\). Every word other than zero and the all-one word has weight between eight and \(n-8\). At \(n=14\) this interval is empty, although the kernel needs at least four words.

The elementary second character moment gives
\[
 n|C|\leq\sum_{c\in C}\bigl(n-2\operatorname{wt}(c)\bigr)^2 .
\]
At lengths 18 and 20, each of the \(|C|-2\) interior words contributes at most 4 and 16 respectively. At length 22, weight 14 is already excluded, and complementing a word excludes weight 8 as well. The remaining interior weights are 10 and 12, so each again contributes at most 4. In each case the moment bound contradicts the lower bound on \(|C|\). [Binary character moment](Green51Hadamard.lean) · [Forbidden relation sizes](Green51MissingLabel.lean)

Consequently \(p\) cannot be the sum of one, three or five of the original labels. Their complements would give forbidden zero sums of length 22, 20 or 18. Inserting \(p\) therefore creates no short even relation. Uniqueness follows because the sum of all labels of every extremal 24-point set is zero. Adding \(p\) to four specified labels and using their unique octad in the completion gives the unique heptad in the original set. [Extremal zero sum](Green51OctadFlats.lean) · [Unique octads](Green51PerfectPacking.lean)

## Deleting labels from an extremal set

For any deleted set \(U\) in an avoiding 24-point set, the number of affine three-spaces in the remaining double is fifteen times the number of zero-sum octads containing \(U\). A nonzero pair sum lies on one flat for each such octad excluding both labels of the pair. These identities give the first six flat counts and the first four uniform point counts below. [Deletion identities](Green51ExtremalFlatCounts.lean) · [Uniform counts](Green51DeletedLabels.lean)

| Labels deleted | 0 | 1 | 2 | 3 | 4 | 5 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Affine three-spaces | 11,385 | 3,795 | 1,155 | 315 | 75 | 15 |
| Flats through each nonzero pair sum | 330 | 120 | 40 | 12 | varies | varies |

Golay code uniqueness and the Witt designs are classical. Delsarte and Goethals proved uniqueness results for unrestricted codes with the Golay parameters. Östergård discusses the known uniqueness of the optimal codes of lengths 23 and 24. The Lean proof above works directly with the given labels in the original ambient space. [Delsarte and Goethals](https://doi.org/10.1016/0012-365X(75)90047-3) · [Östergård](https://doi.org/10.1007/s10623-018-0532-z)

From the pinned Formal Conjectures checkout, set `notebook` to this repository’s path and run `lake env python3 "$notebook/scripts/replay-research" Green51DeletedLabels`.
