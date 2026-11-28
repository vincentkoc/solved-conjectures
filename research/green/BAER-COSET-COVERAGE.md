# Square-order planar sets paired with a Baer coset

Let \(t\ge1\), \(q=t^2\), \(h=q+t+1\), \(j=q-t+1\), and \(v=hj=q^2+q+1\). Let \(D\subset\mathbb Z/v\mathbb Z\) have \(q+1\) elements and exactly one ordered representation of every nonzero difference. Choose any \(q+1\) elements \(B\) of a coset of the subgroup of order \(h\). The cyclic double contains the balanced set
\[
R=2D\ \cup\ (1+2B)\ \subset\ \mathbb Z/(2v)\mathbb Z.
\]

As \(t\to\infty\), the size ratio \(|R|/\sqrt{2v}\) tends to \(\sqrt2\), while \(|R+R|/(2v)\) tends to **\(3/4\)** for every choice of \(D\), coset and deletions. Every full cyclic basis containing \(R\) eventually exceeds each normalized size coefficient below \(\sqrt{5/2}\). Green 33 asks for the existence of unrestricted bases with size coefficient \(\sqrt2\). These conclusions concern the indicated construction and its supersets. [Limit and completion theorems](Green33BaerCoverage.lean) · [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

## The exact count

Use the Chinese remainder coordinates \(\mathbb Z/h\mathbb Z\times\mathbb Z/j\mathbb Z\). The two moduli are coprime. Write \(c=-q\sum_{a\in D} a\), \(A=D-c\), and \(r\) for the second coordinate of \(B-c\). Then
\[
 |R+R|=v-t(j-1)+\frac{(q+1)(q+2)}{2}
       +\begin{cases}0&1+2r=0\pmod j,\\ (h-1)/2&1+2r\ne0\pmod j.\end{cases}
\]
The odd sums cover exactly \(v-t(j-1)\) of their \(v\) residues. Their density tends to one. The even sums occupy about half their parity class. [Finite cyclic formula and CRT map](Green33BaerLayers.lean)

The fixed subgroup in these coordinates is the Baer subgroup. The classical sub-difference-set theorem and the one-point intersections in all other cosets are described in the proof of Jungnickel’s Theorem 6.1, which credits Theorem 4.4 of its reference [17]. In the formal proof the Hall–Menon multiplier \(t\) fixes the centroid-normalized set. Its third power acts by \((a,b)\mapsto(a,-b)\). Uniqueness of each nonzero difference in the fixed subgroup places both endpoints in the central coset. This gives a planar set of size \(t+1\) there, and counting leaves one point in every other coset. [Jungnickel, *Divisible semiplanes, arcs, and relative difference sets*, §6](https://doi.org/10.4153/CJM-1987-051-1) · [Multiplier theorem and attribution](PLANAR-TRIPLE-PEAK.md)

In a noncentral mixed coset the single point translates \(B\), leaving its \(t\) deletions. In the central mixed coset the \(t+1\) points suffice to fill the coset. For the even sums, the ordered pair count on each coset, with its repeated-summand correction, counts every element of \(A+A\) twice because \(A\) is Sidon. This gives all \(h\) points in its central coset and \((h+1)/2\) points in each other coset. The translate of \(B+B\) fills one whole coset because \(2|B|>h\). This proves both cases of the formula. [Weighted Sidon identity](Green33ReflectedLayers.lean) · [Coset counts](Green33BaerLayers.lean)

If \(R\subseteq T\) and \(T+T\) is the whole group of order \(N\), each of the \(N-|R+R|\) missing residues needs a fresh unordered pair. Thus \(2(N-|R+R|)+|R|^2+|R|\le |T|^2+|T|\). Dividing by \(N=2v\) gives the stated completion bound. [Completion inequality](Green33ReflectedLayers.lean) · [Normalized bound](Green33BaerCoverage.lean)

## Checks

At \(q=4\) the finite formula agrees with all 630 choices obtained from the ten cyclic planar sets containing zero and every balanced subset of every opposite coset. At \(q=9\) two translates of a cubic Singer trace line in \(\mathbb Z/91\mathbb Z\) give 4,004 choices. Of these, 572 cover 128 residues and 3,432 cover 134 residues in the double of order 182.

Lean 4.33.1 rebuilt the 27 notebook modules in the import closure. Each module passed independent kernel replay. All 184 printed declarations use only `propext`, `Classical.choice` and `Quot.sound`. A separate elaboration compared the result directly with the pinned positive-modulus statement, including its absolute tolerance at \(\varepsilon=1/100\).
