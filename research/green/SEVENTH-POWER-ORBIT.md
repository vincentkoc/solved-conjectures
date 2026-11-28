# Seventh powers and the BCH projection over the field of order 512

Let \(K\) be a field of order \(2^m\), and let \(L\) be a binary linear map out of \(K\). For \(m\ge4\) with \(m\ne6\), the sumset of the image of
\[
x\longmapsto(x,x^3,x^5,L(x^7))
\]
contains an affine three-dimensional space exactly when \(\dim\ker L\ge3\). This extends the previous threshold to \(m=9\). At \(m=6\), the previous implication still guarantees that discarding at most two dimensions avoids every affine three-space. The unrestricted Green 51 question remains open. [Threshold theorem](Green51BCHSmallFields.lean) · [Previous construction and converse](BCH-COMPRESSION-THRESHOLD.md)

## The orbit of length 73

In a field of 512 elements, every binary subspace of codimension at most three contains at least three distinct nonzero seventh powers. To see this, take a root \(b\) of \(X^9+X+1\). This polynomial divides \(X^{73}-1\), which divides \(X^{512}-X\) and splits over the field. Since \(b\ne1\) and 73 is prime, \(b\) has order 73. Each \(b^i\) is a seventh power because \(21\cdot7\equiv1\pmod {73}\). [Field and orbit proof](Green51SeventhOrbit.lean)

For every binary linear functional \(g\), the bits \(s_i=g(b^i)\) satisfy \(s_{i+9}=s_i+s_{i+1}\) in \(\mathbb F_2\). There are 512 initial nine-bit strings. Lean checks that at most 40 of the next 73 bits, counting the initial nine, equal one in each case. These are weights of the classical binary irreducible cyclic code of length 73. Baumert and McEliece give the general weight-distribution method and tables. The Lean proof computes the needed bound directly from the recurrence. [Kernel certificate](Green51SeventhOrbitWords.lean) · [Baumert and McEliece, *Weights of irreducible cyclic codes*](https://doi.org/10.1016/S0019-9958(72)90354-3)

Write the subspace as the kernel of a map to three bits. Each nonzero output is detected by four of the seven nonzero binary functionals on the output space. Those seven functionals detect at most \(7\cdot40=280\) incidences on the orbit. At most 70 of the 73 outputs are therefore nonzero. The three surviving seventh powers provide the intersection bound, and the Moore determinant argument gives the projection threshold. [Incidence bound](Green51SeventhOrbit.lean) · [Determinant realization](Green51MoorePreimages.lean)

From the pinned Formal Conjectures checkout, run `lake env python3 /path/to/solved-conjectures/scripts/replay-research Green51BCHSmallFields`.
