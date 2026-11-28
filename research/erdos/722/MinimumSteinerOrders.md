# Minimum orders of nontrivial Steiner designs

Let $v>k>r\ge3$ and let $H$ satisfy the block-design predicate in Erdős 722. Put $q=k-r+1$. Apart from the five parameter triples in the table, every such design satisfies
\[
             v\ \ge\ (k-r+2)^2+r-2.
\]
At the smaller exterior-point bound $v=q(q+1)+r-1$, the binomial divisibilities hold exactly in the five cases shown. In ranks at least four, the two Witt designs give the complete unconditional spectrum at equality. [Order bound](Erdos722SteinerOrderGap.lean) · [Equality spectrum](Erdos722WittMinimumOrders.lean.in) · [Pinned Erdős 722](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/722.lean)

| Rank $r$ | Block size $k$ | Order $v$ | Realization or obstruction |
| ---: | ---: | ---: | --- |
| 3 | 4 | 8 | Affine binary quadruples |
| 3 | 6 | 22 | Derive the large Witt design twice |
| 4 | 7 | 23 | Derive the large Witt design once |
| 5 | 8 | 24 | The large Witt design |
| 3 | 12 | 112 | Would give a projective plane of order ten |

## Least order in rank three

Let $Q\ge3$ be a prime power, and give each block size $Q+1$. The least $v>Q+1$ supporting an ordinary Steiner $3$-design is $Q^2+1$ for every $Q\notin\{3,5,11\}$. A quadratic-extension subline design attains the lower bound. The minima for $Q=3,5$ are respectively $8,22$. In particular, the first orders at block sizes $4,5,6,9$ are $8,17,22,65$. The formal statement uses `IsLeast` on all orders with the pinned predicate and excludes the trivial one-block case. [Prime-power minima](Erdos722MinimumTripleOrder.lean) · [Subline construction](../Erdos722ProjectiveSublines.lean) · [Witt specialization](Erdos722WittMinimumOrders.lean.in)

For $Q=11$, Lean gives an unconditional alternative. Either the minimum is 112 and a projective plane of order ten exists, or the minimum is 122. Lam, Thiel and Swiercz proved that the plane does not exist. Bright and coauthors give an independent SAT-based verification. Thus the classical minimum is 122. The Lean classification takes the nonexistence theorem as an explicit hypothesis only for this value of $Q$. The corresponding pinned Erdős 723 declaration is a proof stub, and Left to Solve lists the order-ten branch as open. [Checked alternative](Erdos722ExtremalParameters.lean) · [Lam, Thiel and Swiercz](https://doi.org/10.4153/CJM-1989-049-4) · [Bright et al.](https://arxiv.org/abs/2012.04715) · [Pinned Erdős 723](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/723.lean) · [Left to Solve reduction](https://www.lefttosolve.com/p/Erdos723.erdos_723.variants.leq_11)

## Proof of the gap

Cameron's exterior-point inequality gives $q(q+1)\le v-(r-1)$. The replication number through an $(r-1)$-subset makes the right side a multiple of $q$. If equality fails, the next possible value is at least $q(q+2)$, giving the displayed bound. [Exterior-point inequality](Erdos722SignedSteinerObstruction.lean) · [Cameron, theorem 3A.4](https://doi.org/10.1017/CBO9780511662102)

At equality, apply the binomial test at $i=r-3$. Set $a=q(q+1)$. Cancelling $a$ in $\binom{q+2}{3}\mid\binom{a+2}{3}$ gives $q+2\mid(a+2)(a+1)$. Modulo $q+2$, the two factors are $4$ and $3$, so $q+2\mid12$. This is Hughes's restriction $q=2,4,10$ on extendible planes. The test at $i=r-4$ excludes higher ranks for $q=2,10$, and the test at $i=r-6$ excludes rank six and above for $q=4$. Each of the five surviving triples satisfies every binomial test. [Arithmetic classification](Erdos722PlaneExtensionArithmetic.lean) · [Hughes, *Extensions of designs and groups*](https://doi.org/10.1007/BF02116862)

A point derivative of an $S(3,12,112)$ would be a pair design on 111 points with line size 11. More generally, any pair design on $q^2+q+1$ points with line size $q+1$ yields an actual mathlib `Configuration.ProjectivePlane` of order $q$ for $q\ge2$. Counting the blocks through the empty set and a point gives the number of lines and the size of each pencil. The proof constructs a nondegenerate incidence configuration and uses equality of the numbers of points and lines to recover intersections. [Projective-plane construction](Erdos722SymmetricPairPlane.lean) · [Point derivative](Erdos722DerivedAffine.lean)

## Witness, attribution and replay

The 24-point witness comes from **danielpuri1901**'s six-file kernel proof. It checks the sizes and intersections of 759 octads of the extended binary Golay code and uses incidence counting to establish unique coverage of every five-set. The notebook uses this witness in its original form and applies the point derivative to obtain the 23- and 22-point cases. DeepMind's existing proof-link PR identifies the same witness. The result here concerns minimum orders and the cases of equality. [Pinned Witt proof](https://github.com/danielpuri1901/erdos-lean-formalization/blob/6bd7a2cd9d9a50ba92c3d3b3ae1a2d64e241f4bd/Solution/Witt/Main.lean) · [DeepMind proof-link PR](https://github.com/google-deepmind/formal-conjectures/pull/7660) · [Curtis on the binary Golay code and octads](https://www.lms.ac.uk/sites/default/files/4.%20Curtis%20-%20Error%20Correction%20and%20the%20Binary-Golay%20Code.pdf)

The independent Lean 4.33.1 replay checked 18 notebook and adapter modules and all six original Witt modules. All 18 public theorems in the changed sources and the external witness passed the standard-axiom audit. A direct comparison checked the exact Erdős 722 and 723 quantifiers, the original Witt target, the four numerical minima above and the divisibilities at order 112.

From the pinned Formal Conjectures Lake environment, run the notebook's `research/erdos/722/replay-witt-minimum` under `lake env`. Supply `--archive` to reuse the pinned public source archive. The runner verifies the source digest and builds in a temporary directory. The rank-three lower bound and the projective-plane reduction are also available in the ordinary notebook replay as `Erdos722ExtremalParameters`. The full arbitrary-rank eventual existence theorem remains to be formalized in the pinned file. [Replay runner](replay-witt-minimum) · [Original statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5495) · [Left to Solve](https://www.lefttosolve.com/p/Erdos722.erdos_722) · [OMA rank reduction](https://github.com/lefttosolve2/open-math-agents/pull/17505)
