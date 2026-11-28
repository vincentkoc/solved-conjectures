# An arbitrary second layer opposite a Singer line

Put $v=q^2+q+1$. In the cyclic group of order $2v$, take $S=2D\cup(1+2B)$, where $D$ is a binary cubic Singer line and $B$ is **any** set of $q+1$ labels in the cyclic group of order $v$. Along every sequence of such frames with $q\to\infty$, the following statements hold for all sufficiently large indices.

- At least $q\sqrt q-2q$ residues are missing from $S+S$.
- Every ordinary basis $T$ of the same group has at least $\sqrt q-4$ elements outside $S$. Its elements may lie in either parity and it may discard elements of $S$.

The size of $S$ is exactly $2(q+1)$, so its size divided by $\sqrt{2v}$ tends to $\sqrt2$. These estimates exclude exact coverage by this balanced construction and by repairs using $o(\sqrt q)$ fresh elements. The lower bound on the missing proportion tends to zero, and the required number of fresh elements is sublinear in $q$. The asymptotic size coefficient of full repairs remains open. Green 33 allows unrestricted cyclic moduli and bases. [Pinned DeepMind question](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

## The two counts

Write $b=|B|$, $h=v-|D+B|$, and $r(c)=|B\cap(c-D)|$. The lines of the projective plane are the sets $c-D$. Each pair of distinct points lies on exactly one line. If all line occupancies are at most $m$, counting ordered pairs of distinct points gives $b(b-1)\le m((q+1)b-v+h)$. For a line of positive occupancy $r$, each missed line meets it in one point. Counting through its outside points gives $(q+1-r)(r+q-b)\le h$.

Both counts occur in the proof of Theorem 3.2 of Blokhuis, Brouwer, Szőnyi and Weiner, following Erdős and Lovász. Their bound with the integer part of the square root is sharper for the incidence problem. We formalize the counts for an arbitrary perfect difference set in a finite abelian group. They recover Bruen’s full-cover alternative. For $b=q+1+s$, either $B$ contains a reflected line or $s^2\ge q$. [Blokhuis et al., §3.1](https://pure.tue.nl/ws/portalfiles/portal/3536392/696271935668854.pdf) · [Bruen, *Blocking Sets in Finite Projective Planes*](https://doi.org/10.1137/0121041)

When $b=q+1$, the counts give either $h\ge q\sqrt q-2q$ or a reflected line containing all but fewer than $\sqrt q$ points of $B$. The missed mixed sums appear in the odd coset. In the second case, replacing fewer than $\sqrt q$ odd points can cover at most $2(q+1)\sqrt q$ formerly missing sums. The reflected seed covers a proportion tending to $7/8$ for every sequence of axes. This leaves at least $2q\sqrt q-2q$ holes eventually in the second case. A fresh point meets only the opposite old layer when forming an odd sum. Counting that cost separately from the total sumset cost gives the $\sqrt q-4$ bound. [Reflected Singer coverage](https://github.com/vincentkoc/solved-conjectures/pull/376)

## Formal scope

The binary declarations are `binary_holes` and `binary_repairs` in `Green33SingerBlockingLayers`. They use the cubic frames of the prior binary theorem and allow every second layer of size $q+1$ and every replacement ordinary basis. `balanced_size_limit` proves the radical normalization for any two balanced layers with the first a perfect difference set and the modulus growing. `all_characteristics` gives both estimates for a projectivized hyperplane in any finite cubic field extension under the explicit, pointwise Deligne rank-four bound. The finite incidence, mixed repair and parity estimates are unconditional. [Lean declarations](Green33SingerBlockingLayers.lean) · [All-characteristic analytic input](https://github.com/vincentkoc/solved-conjectures/pull/381)

We enumerated all 21,099 second layers at $q=2,3,4$, checking both occupancy inequalities and comparing the parity counts with direct cyclic addition. Respectively 7, 13 and 21 choices covered every odd residue. At each order at least one choice covered the whole double.
