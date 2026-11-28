# How often the same labels lose coverage at nearby orders

Suppose $N\to\infty$, $A\subseteq\mathbb Z/N\mathbb Z$, $|A|/\sqrt N\to\sqrt2$, and $|A+A|/N\to1$. Use the least representatives of $A$ as a fixed set of labels when changing modulus. Given $\varepsilon>0$, put $h=\min(\varepsilon,1/3)$. For **every fixed** $0<\delta\le h/4$, and eventually along the family, more than a $2/3-\varepsilon$ fraction of the next $\lfloor\delta N\rfloor$ moduli miss at least an $h/32$ fraction of their residues. This counts actual cyclic sumsets, including repeated summands. The starting modulus is excluded. [Window theorem and coverage predicate](Green33FoldedTails.lean)

There is also a lower bound for every recast in the range $N\le m\le2N$. Along any choice with $m/N\to s$, the coverage fraction has limit inferior at least $1-s/4$. In particular, an arbitrary choice with $m/N\to1$ from above has limit inferior at least $3/4$. These statements concern the given labels. The existence of a critical family with the assumed size and coverage remains open. Exact two-bases satisfy the coverage hypothesis. [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Equivalence for almost-covers](APPROXIMATE-COVERS.md)

## Counting folds

Write $C$ for the ordinary sumset of the least representatives and $L_m=|C|-|C\bmod m|$. Let $k=|A|$ and let $E$ be the maximum absolute difference between the number of labels in $[0,w)$ and $wk/N$, over $0\le w\le N$. For integers $m\ge d\ge N$, put $T=\max(0,\lfloor k-dk/(2N)+2E\rfloor)$. Then
\[
  2L_m\le (T+1)(T+2)+4k.
\]
Each fold corresponds to a pair $z,z+m$ in $C$. If $2z+d\le2N$, count it by its lower sum. Otherwise count it by its upper sum. In the first case the two increasing label ranks sum to at most $T$. In the second, the two reversed ranks obey the same bound. Each rank triangle contains $(T+1)(T+2)/2$ ordered pairs. A sum outside the diagonal image has at least two orderings. This accounts for the additive $4k$. [Finite bound](Green33FoldedTails.lean) · [Rank estimates](Green33RankSimplex.lean)

For $N\le d\le2N$ with $d/N\to s$, the prefix discrepancy is $o(\sqrt N)$. The finite bound gives $L_m/N\le (2-s)^2/4+o(1)$ uniformly for $m\ge d$. For a band $[a,b)$ with $a\ge N$, $a/N\to s$ and $b/N\to t>s$, and $t<2$, put
\[
 u=\frac{(2-s)^2}{4},\qquad V=\frac{(2-s)^4-(2-t)^4}{24(t-s)}.
\]
The earlier band theorem gives limiting mean $V$ for $L_m/N$. For $\gamma\le u$ and $p\le1$, the strict inequality $\gamma+(u-\gamma)p<V$ forces more than a fraction $p$ of the band to have $L_m\ge\gamma N$ eventually. Shrinking a fixed relative window toward $s=1$ gives $V\to1/6$ and $u\to1/4$, hence the two-thirds bound. The constants here give lower bounds on the frequency of losses. [Band mean and one-sixth witness](NEARBY-MODULI.md) · [Band prevalence](Green33FoldedTails.lean)

## Repairing the seed

In any additive commutative monoid, let $B,D$ be finite sets, $k=|B|$, and $R=|B\cap D|$. Every new sum in $(B+B)\setminus(D+D)$ needs an unordered pair outside $(B\cap D)^2$. Counting unordered pairs with repetition gives
\[
 R(R+1)+2|B+B| \le k(k+1)+2|D+D|.
\]
At a nearby order where the original labels lose a sixth, this limits how many old labels an exact basis can retain. For every $\sqrt{5/6}<r\le1$ there exists $\tau>0$ such that, for every $\eta>0$ and eventually along the original family, **some** $N<m\le(1+\eta)N$ has the following property. Every exact basis $B$ at $m$ with $k(k+1)\le(2+\tau)m$ retains fewer than $rk$ of its labels from the original set. Thus every prescribed fraction below $1-\sqrt{5/6}\approx8.71\%$ must be new at a witness, with the corresponding budget tolerance. This last conclusion uses the earlier one-sixth witness and permits the witness to depend on the window. [Repair capacity and witness theorem](Green33FoldedTails.lean) · [Earlier witness](NEARBY-MODULI.md)

## Verification and scope

The independent Lean 4.33.1 replay rebuilt 17 notebook modules and checked 130 axiom prints, including all nine declarations in the new module. The canonical Green declaration was compared by definitional equality, and the window theorem was separately applied under the canonical exact basis condition. An exhaustive finite check covered 135,166 seed–threshold–modulus triples through order ten and 349,524 ordered seed pairs for the repair inequality through order nine. The DeepMind issue and merged PR concern the original statement. Left to Solve listed the question as open. Targeted DeepMind, Open Math Agents and personal tracker searches found no matching prevalence or repair result. [Original issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33)
