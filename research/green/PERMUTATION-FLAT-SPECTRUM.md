# Five possible largest-flat counts from a four-dimensional permutation

The zero-offset paired construction in dimension 15 has exactly five possible counts of affine four-spaces in its double. They are **1, 2, 3, 5 and 31**. Each occurs for a 32-point set whose double avoids every linear three-space and has maximum coset dimension four. This gives five affinely inequivalent examples at the minimum ambient dimension and cardinality. Exhaustiveness refers to the construction as the permutation varies. Green 51's density problem remains open. [Exact spectrum and ambient witnesses](Green51FlatSpectrum.lean) · [Minimum dimension and size](FOUR-SPACE-DIMENSION.md) · [Pinned problem](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

## Counting by constant derivatives

Let \(q(x)=(x_i x_j)_{i\le j}\) for \(x\in\mathbb F_2^d\), and let \(f\) permute that space. Place labels \((q(x),0,0)\) and \((q(x),1,f(x))\) over each \(x\). The label set fits in dimension \(\binom{d+2}{2}\). For \(d\ge4\) its double always contains the affine \(d\)-space \(\{(0,1,y)\}\). [Construction and avoidance](PERMUTED-PAIR-FLATS.md)

Write \(H=\{t:f(x+t)+f(x)\text{ is constant in }x\}\) and \(k_t=f(t)+f(0)\). For each nonzero \(t\in H\), put \(h_t(x)=q(x)+q(x+t)\). The points over this chord family with middle coordinate zero form one affine \(d\)-space. The points with middle coordinate one form a second affine \(d\)-space exactly when \(f\) induces an affine map from the quotient by \(\langle t\rangle\) to the quotient by \(\langle k_t\rangle\). The odd height determines the chord. A flat mixing the two middle coordinates would have at most four points. These possibilities exhaust the nonvertical largest flats. [Chord geometry](Green51ChordSheets.lean) · [Quotient criterion](Green51SheetClosure.lean) · [Count formula](Green51SheetCount.lean)

Let \(s=\dim H\). An affine permutation gives \(2^{d+1}-1\) flats. For a nonaffine permutation the count is \(2^s\) or \(2^s+1\), with \(s\le d-2\). At \(s=d-2\) the count is always \(2^s+1\). The proof uses the defect
\[
\Delta(x,y)=f(x)+f(y)+f(0)+f(x+y).
\]
A nonzero defect must equal \(k_t\) for every \(t\) contributing an odd flat, so injectivity allows at most one such \(t\). When the quotient by \(H\) has four elements, every pair with nonzero defect uses two distinct nonzero cosets. Exchanging the cosets or replacing one by their sum preserves the defect. Thus all nonzero defects have one value \(w\). Choose \(t\) with \(k_t=w\). The equality \(\Delta(x,t)=w\) would force \(f(x)=f(x+t)\), hence \(\Delta(x,t)=0\) for every \(x\). This supplies the required direction. [Four-coset proof](Green51LinearStructures.lean) · [Rank and counts](Green51StructureCounts.lean)

The space \(H\) is the classical space of linear structures of a vectorial Boolean function. Baudrin et al. give its subspace and codimension properties in Lemma 9 and Corollary 10. The Lean proof derives the properties it uses directly. [Baudrin et al., §6.3](https://opencryptology.org/2024/1678/versions/20260428T172000Z.pdf)

## Examples

| Permutation on four bits | Nonzero constant derivatives | Odd flats from those directions | Total four-spaces |
| --- | ---: | ---: | ---: |
| Inversion in \(\mathbb F_{16}\), fixing zero | 0 | 0 | 1 |
| Inversion in \(\mathbb F_8\) on three bits, preserving the fourth | 1 | 0 | 2 |
| Toggle the fourth bit when all three low bits are one | 1 | 1 | 3 |
| Toggle the fourth bit when both lowest bits are one | 3 | 1 | 5 |
| Identity | 15 | 15 | 31 |

The Lean certificate checks that all five permutations are involutions and evaluates the direction-count formula. Set `notebook` to this repository's path and run `lake env python3 "$notebook/scripts/replay-research" Green51FlatSpectrum` from the pinned Formal Conjectures checkout.
