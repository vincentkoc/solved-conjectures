# Two-bit BCH projections in odd field degree

There is a set of 512 points in the binary 29-cube whose sumset contains no affine five-space. Take \(K=\mathbb F_{512}\) and the graph
\[
 A_L=\{(x,x^3,x^5,L(x^7)):x\in K\}.
\]
Here \(L\) consists of two independent absolute trace coordinates. Four is the minimum, over all binary maps \(L:K\to\mathbb F_2^2\), of the largest affine dimension in \(A_L+A_L\). On the original cube this gives \(\operatorname{guaranteedMaxCosetDim}(29,\alpha)\le4\) for every \(\alpha\le512/2^{29}\). The full Green 51 question remains open. [Witness and minimum](Green51NinePencils.lean) · [Pinned Green 51](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/51.lean)

## When the field degree is coprime to three

Write \(m=2k+1\ge3\) for the binary field degree. If \(3\nmid m\), **every** nonzero projection \(L\) of rank at most two gives largest dimension \(k+1\). The target of \(L\) can be any finite-dimensional binary vector space. For example, the largest dimension is four for every such projection in degree seven and six for every such projection in degree eleven. [Odd-degree theorem](Green51OddPencils.lean)

The two coordinates give alternating forms through the bracket \([x,y]=xy(x+y)\). They vanish together on a \((k+1)\)-space. A nonzero scalar \(s\) moves that space into the absolute trace kernel. The bracket scales by \(s^3\). Since \(7\) is coprime to \(2^m-1\), one can choose a shift \(t\) satisfying \(t^7s^3=1\). Lifting the scaled subspace gives the required affine space in the sumset. The bound in the other direction follows from the radical dimension of a nonzero scalar Gold form. The odd-power graph comes from the classical BCH construction. Gow and Quinlan discuss common isotropic subspaces, and Coşgun gives the trace-form background. [Simultaneous isotropy](Green51TwoAlternating.lean) · [Gow and Quinlan, §1](https://maths.ucd.ie/~rodgow/alternatingnew.pdf) · [Coşgun, §2](https://doi.org/10.1016/j.ffa.2017.11.005) · [Bose and Ray-Chaudhuri](https://doi.org/10.1016/S0019-9958(60)90287-4)

## Why degree nine permits a smaller maximum

Choose \(g\in K\) satisfying \(g^9=g+1\) of order 73. Set \(\beta=g^3+g^4+g^5+g^7\) and take \(L(z)=(\operatorname{Tr}(z),\operatorname{Tr}(\beta z))\). A five-space in the double would rescale to a common five-dimensional isotropic subspace \(U\) for the bracket forms with coefficients \(1,\beta\). For the first form the radical is the binary span of \(1\), so \(U=U^\perp\). Starting with \(u_0=1\), this forces four more specified vectors into \(U\) by the recurrence
\[
 u_i^4+u_i=\beta^2u_{i-1}^4+\beta u_{i-1}.
\]
The obstruction is whether a seventh-power multiple carries all five vectors into the absolute trace kernel. [Forced vectors](Green51NineRadicals.lean) · [Order-73 root](Green51SeventhOrbit.lean)

The seventh powers are exactly \(1,g,\ldots,g^{72}\). For \(w_j=\operatorname{Tr}(g^j)\), the relation for \(g\) gives \(w_{j+9}=w_{j+1}+w_j\). A 73-bit certificate checks that for each scale \(g^j\) at least one of the five traces \(\operatorname{Tr}(g^ju_i)\) is nonzero. This excludes the five-space. The lower bound of four holds for every two-bit map by restricting its two alternating forms to seven dimensions. [Trace certificate](Green51NineTraceWord.lean) · [Lower bound](Green51BCHFourForces.lean)

Replay from the pinned Formal Conjectures checkout with `lake env python3 /path/to/solved-conjectures/scripts/replay-research Green51NinePencils`.
