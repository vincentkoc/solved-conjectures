# Stability near the sharp number of missing directions

Let $A$ be a subset of $\mathbb F_2^{2s+2+r}$, with $s\ge1$, and let $D$ be the complement of $A+A$. Suppose the density of $A$ exceeds $h_{2s}=\tfrac12-\binom{2s}{s}/2^{2s+1}$ and $A+A$ contains no affine hyperplane. Put $g=2s+3$. Its largest affine subspace has dimension exactly $2s+r$ whenever
$$
8|D|>\min(5g+12,\,4g+20)\,2^r.
$$
The sharp upper bound on $|D|$ is $g2^r$. In dimension 16 with $s=6$ and $r=2$, the criterion applies from 41 missing directions through the maximum of 60. [Green 51 theorem](Green51MissingStability.lean) · [Sharp upper bound](SHARP-MISSING-COUNT.md)

The proof gives a completion theorem for binary sets of odd girth at least $g$, meaning every odd zero-sum subset has at least $g$ elements. Take an odd $g\ge5$ and a set $D\subseteq\mathbb F_2^n$ of odd girth at least $g$. Assume no linear functional takes the value one on all of $D$. If
$$
8|D|>\min(5g+12,\,4g+20)\,2^{n+1-g},
$$
there is a greatest superset $U$ of $D$ with odd girth at least $g$. It consists of all cosets of a single shortest $g$-circuit by a complement to the span of the circuit. Consequently $|U|=g2^{n+1-g}$. A new direction belongs to $U$ exactly when adjoining it to $D$ preserves the odd-girth condition. [Greatest extension](Green51GreatestExtension.lean)

A fibre containing at least five points lies in a translated copy of the circuit. Two such fibres constrain all points in their sum fibre, even after other directions are adjoined. When more than five eighths of the fibres qualify, their centres extend to a linear map. At six points per fibre a four-fibre argument also preserves every pair-sum relation. More than half of these fibres then suffice. [Circuit words](Green51PartialCircuitWords.lean) · [Dense additivity](Green51DenseAdditivity.lean) · [Fibre structure](Green51RichCircuitSlices.lean) · [Linear sections](Green51RichSliceSections.lean)

Geelen proved the sharp binary odd-girth bound and constructed circuit examples of equality. The scalar extension argument here uses its girth-five case, also part of the classical theory of large sum-free sets in binary spaces. The general Green 51 density function remains open. [Geelen](https://arxiv.org/abs/1401.5769) · [Clark and Pedersen](https://doi.org/10.1016/0097-3165(92)90019-Q)
