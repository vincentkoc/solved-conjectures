# The exact planar triple count at the centroid

Let \(D\) be a subset of size \(q+1\) in a finite abelian group such that each nonzero element occurs exactly once as an ordered difference of elements of \(D\), with \(q>0\). Then the group has order \(v=q^2+q+1\). Set \(c=-q\sum_{d\in D}d\), so \((q+1)c=\sum D\). At the center \(3c\) the exact number of ordered triple sums, including repeated summands, is
\[
r_{3,D}(3c)=
\begin{cases}
2q+1 & q\equiv0\pmod3,\\
2q   & q\equiv1\pmod3,\\
2q+2 & q\equiv2\pmod3 .
\end{cases}
\]
This holds for every abelian planar difference set, with no field construction or prime-power assumption on \(q\). For the cyclic cubic Singer labels over each prime \(p\ge10000\), \(3c\) is the unique global maximizer of the ordered triple count. In particular the unusual label previously isolated by the cubic discriminant has an intrinsic description using the sum of the labels. [Exact counts and uniqueness](Green33PlanarMultipliers.lean) · [Cubic pencil classification](PRIME-SINGER-EXCEPTION.md)

## Multiplier and orbit argument

The prime multiplier step is the classical theorem of Hall for cyclic planar difference sets, in its abelian form. Menon generalized the multiplier theorem to abelian groups. Turyn gives the group-ring criterion and discusses that generalization. Here is the specialization formalized in Lean. For each prime \(\ell\mid q\), form \(A=\sum_{d\in D}[d]\), \(A^-=\sum_{d\in D}[-d]\) and \(J=\sum_{g\in G}[g]\) over \(\mathbb F_\ell\). Perfectness gives \(AA^-=J\), and \(AJ=J\) since \(q+1\equiv1\bmod\ell\). Frobenius then gives \(A^{(\ell)}A^-=A^{\ell-1}J=J\). Every mixed difference occurs at least once. The notebook's blocking-set theorem at the exact line size gives \(\ell D=D+t\). Summing this identity shows that translating \(D\) by \(-c\) simultaneously normalizes every multiplier dividing \(q\). [Hall, *Cyclic projective planes*](https://doi.org/10.1215/S0012-7094-47-01482-8) · [Turyn, *The multiplier theorem for difference sets*](https://doi.org/10.4153/CJM-1964-039-1) · [Blocking alternative](Green33SingerBlockingLayers.lean)

On \(D-c\) the map \(x\mapsto qx\) has cube equal to the identity, and \(x+qx+q^2x=0\). The Sidon property determines the remaining two summands up to order once the first summand is fixed. It contributes two completions at every nonfixed point and one at each fixed point. The number of fixed points is congruent to \(q+1\bmod3\). Each fixed point lies in the 3-torsion subgroup. Its order is a power of three dividing \(v\), and \(9\nmid v\). If \(q\not\equiv1\bmod 3\) then \(3\nmid v\) as well. These facts determine the three values in the table. [Perfect-set Sidon property](Green33PerfectDifferenceCenters.lean) · [Orbit count](Green33PlanarMultipliers.lean)

For a prime Singer line, the previously established upper bound \(p+80(\lfloor\sqrt p\rfloor+1)+10\) holds outside at most one center. For \(p\ge10000\) that bound is strictly below \(2p\), whereas \(3c\) has at least \(2p\) triples. The exceptional center is thus the unique maximizer. As a finite check, exhaustive enumeration of all difference sets containing zero at \(q=2,3,4,5\) gave respectively 6, 16, 10 and 60 sets. Every centroid count agreed with the formula. [Uniform prime triple estimate](Green33PrimeSingerCounts.lean)

## Scope

Green 33 concerns unrestricted ordinary two-sum bases of positive cyclic order with normalized size tending to \(\sqrt2\). This result determines a three-sum statistic of perfect difference sets, and identifies the unique maximum in the large-prime cubic Singer case. A direct Lean comparison imports the pinned declaration and proves that at every positive cyclic order, a planar line of plane order at least two satisfies the centroid count and misses at least one ordinary two-sum. The unordered pairs number at most \(\binom{q+2}{2}<q^2+q+1\). The unrestricted two-sum basis question remains open. The primary multiplier theorem is attributed above. Tracker searches for the planar multiplier and exact triple result found no matching implementation in DeepMind, Open Math Agents or the personal notebook. [Pinned DeepMind declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33)

Lean 4.33.1 rebuilt the 24-module import closure from source. Each module passed independent kernel replay. All 151 axiom reports, including those for the four exported declarations here, contained only `propext`, `Classical.choice` and `Quot.sound`.
