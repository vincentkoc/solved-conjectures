# Green 33 for truncations of one regularly growing set

Let $S\subseteq\mathbb N$, write $k(x)=|S\cap[0,x)|$, and set $A_q=(S\cap[0,q))\bmod q$. Suppose $k(x)/\sqrt{x}\to c$. If $|A_q+A_q|/q\to1$ along a sequence of moduli tending to infinity, then
\[
c\ge\sqrt{8/\pi}\approx1.595769.
\]
At the Green 33 coefficient $c=\sqrt2$, the coverage over **all** moduli satisfies
\[
\limsup_{q\to\infty}\frac{|A_q+A_q|}{q}
\le 1-\frac{(1-\pi/4)^2}{2-\pi/4}
\approx 0.96208309.
\]
Thus even a sparse sequence of orders cannot have coverage tending to one for such an $S$. Green's original question allows a separate finite set at each order. The notebook construction with coefficient $18/\sqrt{130}\approx1.578704$ on large multiples of $130$ also falls below this fixed-set threshold. [Lower bound and critical coverage](Green33RegularTruncations.lean) · [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Construction on multiples of 130](ALL-SEED-MULTIPLES.md)

## Counting near the last residue

Take $0<t<1$ and inspect the residues from $\lfloor t^2q\rfloor$ to $q-1$. An occupied residue contributes at least two ordered representations unless all its representations are diagonal. Discarding diagonal residues costs at most $k(q)$. Integer sums in the window either lie below $q$ or wrap once.

For an element $x\in S$, its rank is $k(x)$. Regular growth yields
\[
 \max_{x\le q}\left|k(x)^2-c^2x\right|=o(q).
\]
Consequently the ordered rank pairs for the unwrapped sums lie in a quarter annulus of squared radii $c^2t^2q-o(q)$ and $c^2q+o(q)$. Its normalized count tends to $\pi c^2(1-t^2)/4$. In the wrapped case both labels must lie in $[\lfloor t^2q\rfloor,q)$, which has $(c(1-t)+o(1))\sqrt q$ labels of $S$. If $p$ is any subsequential coverage limit, the resulting inequality is
\[
  2(1-t^2)\le \frac{\pi c^2}{4}(1-t^2)+c^2(1-t)^2+2(1-p).
\]
For $0<c<\sqrt{8/\pi}$ put $a=1-\pi c^2/8$. Taking $t=c^2/(2a+c^2)$ gives $1-p\ge a^2/(a+c^2/2)$. This is the optimized bound from this window inequality. [Finite annulus, window inequality and limsup bound](Green33RegularTruncations.lean)

## Attribution and verification

Stöhr's lower bound for an ordinary integer basis of order two is $\limsup k(x)/\sqrt{x}\ge\sqrt{8/\pi}$. Nathanson records it as Theorem 4 in *Cassels Bases*. The result here assumes a limit for the counting function and only modular near-coverage along a subsequence. Its proof includes both possible integer lifts of each residue. Targeted DeepMind, Open Math Agents and personal tracker searches found no matching cyclic truncation theorem. Left to Solve lists the original Green 33 question as open. [Stöhr](https://doi.org/10.1515/crll.1955.194.111) · [Nathanson, Theorem 4](https://www.theoryofnumbers.com/melnathanson/pdfs/nath2010-138.pdf) · [Formalization issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33)

Replay **Green33RegularTruncations** with the [notebook runner](../../scripts/replay-research). Fresh Lean 4.33.1 compilation and independent kernel replay checked the module and its 12 axiom reports. Finite checks covered 98,304 seed–window choices through order 12, including 64,023 nonempty annuli with positive inner threshold, and 251 integer disk radii.
