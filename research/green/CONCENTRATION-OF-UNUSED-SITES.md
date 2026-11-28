# Where the unused sites occur

Give each affine class of dense binary doubles equal weight. Write \(h\) for the number of unused sites in a full circuit carrier. Almost every class has these sites in fewer than \(64(\lfloor\log_2 h\rfloor+2)\) rows. In particular, at least one row contains a positive constant times \(h/\log h\) unused sites.

Let the carrier have \(2s+3\) rows and \(2^r\) sites per row, where \(s\ge5\), \(10\le h\le 2s+3\), \(h<2^r\), and \(r\ge h-1\). Fix any spanning reference circuit of this size. For each integer \(B\ge64(\lfloor\log_2 h\rfloor+2)\), at most a fraction \(2^{-\lfloor Bh/8\rfloor}\) of classes admit a presentation with at least \(B\) incomplete rows. This counts distinct affine classes of actual doubles \(A+A\) at the density threshold and codimension-two condition in the [stable class theorem](STABLE-FIBRE-AND-ROW-DIMENSIONS.md). A site is unused when it belongs to the carrier but lies outside the mask \((A+A)^c\). [Family, presentations and class count](Green51DenseOmissionRowTail.lean)

The same bound holds for classes that admit a presentation with at most \(L\) unused sites per row whenever \((B-1)L<h\). For example, take \(h=2^{20}\) and \(B=1408\). Except for a fraction at most \(2^{-184549376}\), every presentation on the reference circuit has a row with at least 746 unused sites. The theorem allows the representative and coordinates to vary within the affine class. [Large row bound](Green51DenseOmissionRowTail.lean)

### Counting by the number of incomplete rows

If precisely \(b\) rows contain unused sites, pick one unused site in each as an origin and subtract it from the other sites of that row. This leaves \(m=h-b\) labelled vectors. Record the row of each vector and the kernel of the resulting binary linear map on \(m\) coordinates. Equal records identify a single linear fibre map and a translation in each row. The empty rows can then be matched in any order. The number of pairwise inequivalent presentations is at most
\[
 b^m(m+1)2^{\lfloor m^2/4\rfloor+m}.
\]
This bound is independent of both the original number of rows and the fibre dimension. [Removing origins](Green51AnchoredOmissionRows.lean) · [Restoring rows](Green51RestoreEmptyRows.lean) · [Counting the records](Green51ActiveRowPresentations.lean)

Summing over \(b\ge B\) and comparing with the [one-row lower bound](GROWTH-OF-STABLE-AFFINE-CLASSES.md) gives the stated fraction. For the large-row conclusion, fewer than \(B\) rows of capacity \(L\) can hold at most \((B-1)L\) unused sites. The binary subspace count underlying the comparison belongs to classical code enumeration. The general guaranteed-coset-dimension question in Green 51 remains open. [Finite estimate](Green51OmissionRowCharge.lean) · [Summed bound](Green51OmissionRowTail.lean) · [Wild, *The asymptotic number of binary codes and binary matroids*](https://arxiv.org/abs/cs/0408011) · [Pinned problem](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

From the pinned Formal Conjectures checkout, run `lake env python3 "$runner" Green51DenseOmissionRowTail` using the [notebook replay setup](../README.md#replay).
