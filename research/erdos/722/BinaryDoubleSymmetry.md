# Automorphisms and isomorphism classes of switched Steiner quadruple systems

Fix $d\ge7$, write $n=2^d$ and $b=\binom{n}{3}/4$, and take the binary affine Steiner quadruple system $H$ on $n$ points. Its $b$ blocks have independent binary switches. Among the $2^b$ resulting labelled systems on $2n$ points, the proportion having a symmetry beyond the vertical check group is at most $2^{-E}$, where $E=\lfloor n^3/1024\rfloor$. Every other system has full automorphism group elementary abelian of order $2n$. At $n=128$ this gives at least $(1-2^{-2048})2^{85344}$ distinct labelled systems on 256 points with full group of order 256. The construction and group isomorphism use the actual finite host labels. [Construction and group theorem](Erdos722BinaryDoubleSymmetry.lean) · [Finite exceptional bound](Erdos722CubicSwitchBound.lean)

Let $N$ count this family's isomorphism classes under **all** permutations of the $2n$ points, $A=|\mathrm{Aut}(H)|$, $g=A2^n$ and $m=2n\,2^b$. Then
$$
0\le Ng-m\le 2^{b-E}.
$$
In particular $N$ has main term $m/g$ with relative error between zero and $2^{-E}/(2n)$. The same estimate holds over any separating base of order $2^d$ with $m=c2^b$ and $c$ the number of its binary parity checks. The finite formulas keep $A$ as the exact order of the base automorphism group. [Class-count theorem](Erdos722BinaryOrbitEstimate.lean) · [Fixed-point formula](Erdos722SwitchMassFormula.lean)

## How the point pairs are recovered

A check is a function to $\mathbb F_2$ whose sum on each block vanishes. On the double every check has the form $h(x,i)=u(x)+ci$ with a single slope $c$. The blocks containing two complete point pairs force the slope to be constant. The transversal blocks then impose $\sum_{x\in B}u(x)=c s_B$. A switch $s$ is a coboundary when it is the list of block sums of some point function. [Parity decomposition](Erdos722QuadrupleParityChecks.lean)

In a separating base the checks distinguish every two points. For a non-coboundary double, two points agree on all checks exactly when they lie over the same base point. Thus its fibres are intrinsic. Coboundary doubles are separating and form one isomorphism class. For every two switches $s,t$, unrestricted isomorphism is equivalent to the existence of a base automorphism $\sigma$ and a point flip $f$ such that
$$
t_{\sigma B}=s_B+\sum_{x\in B} f(x)
\quad\text{for every base block } B.
$$
For a coboundary the criterion describes when an isomorphism exists. Individual automorphisms of such a double can mix the original fibres. [Intrinsic fibres](Erdos722IntrinsicDoubleFibres.lean) · [Unrestricted isomorphism criterion](Erdos722SwitchIsomorphismLaw.lean)

In the explicit base, successive all-zero doublings add one free binary check each, starting with two checks on one point. This gives exactly $2^{d+1}$ checks and preserves separation. Evaluating the checks embeds the point set as a translate of a binary additive subgroup. Four distinct points form a block exactly when their evaluations sum to zero. These facts identify the base with the affine plane design on $\mathbb F_2^d$. [Binary bases](Erdos722BinaryCheckBases.lean) · [Intrinsic affine coordinates](Erdos722AffineCheckModel.lean)

## Why the exceptional fraction is small

In any Steiner quadruple system of order $n$, a nonidentity automorphism moves at least $n/2$ points. Fix a moved point $x$ and a fixed point $a$, when one exists. Each other fixed point determines a distinct block through $x,a$, since three fixed points in one block force the fourth point to be fixed. There are $(n-2)/2$ blocks through the pair. A fixed block through $x$ also contains $\sigma x$, so the point degree minus the pair degree counts at least $(n-2)(n-4)/6$ moving blocks through $x$ for $n\ge4$. Counting incidences with moved points gives at least $n(n-2)(n-4)/48$ moved blocks. [Point motion](Erdos722QuadruplePointMotion.lean) · [Block motion](Erdos722QuadrupleBlockMotion.lean)

For fixed $\sigma,f$, the block equations determine every bit in a cycle of the induced block permutation from any one bit. Moving $2q$ blocks therefore costs at least $q$ free choices. A union bound controls exceptional switches, including a separate allowance of at most $2^n$ coboundaries. Burnside's lemma gives the sharper class count. The identity base permutation contributes exactly $c2^b$ fixed switches summed over all flips. The remaining rows contribute at most $A2^n2^{b-q}$. [Twisted assignments](Erdos722TwistedSwitchCounts.lean) · [Exceptional switches](Erdos722ExceptionalSwitches.lean) · [Orbit action](Erdos722SwitchOrbitAction.lean)

## Scope and sources

The host predicate is `Finset.IsBlockDesign 3 4`. The bounds count one specified family at orders $2^{d+1}$, with $d\ge7$ for the cubic estimates. The isomorphism criterion holds for nonempty separating bases without this cutoff. Keevash proved the general eventual existence theorem. The earlier notebook construction counted all projection-compatible labelled lifts and gave a lower bound on unlabelled counts after allowing for all point permutations. [Pinned Erdős 722](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/722.lean) · [Earlier doubling classification](QuadSwitchCounts.md)

Tonchev derived a labelled formula at binary rank one above the minimum, established exponential growth of the number of isomorphism classes, and classified order 16 at rank 12. D. V. Zinoviev and V. A. Zinoviev describe fixed-corank constructions and enumeration. The contribution here is a checked exceptional fraction, a full-group identification for the complementary switches, and an unrestricted class estimate with explicit relative error. Historical priority for these bounds is unestablished. [Tonchev (2003)](https://doi.org/10.1002/jcd.10036) · [Zinoviev and Zinoviev (2013)](https://www.moi.math.bas.bg/oc2013/p33.pdf)

The DeepMind entries concern the statement and packings. Left to Solve lists the general problem as research solved. The Open Math Agents contributions concern a reduction and its rank-one subproblem. The live title and statement searches located no corresponding formalization of the cubic estimates. [DeepMind statement](https://github.com/google-deepmind/formal-conjectures/pull/5495) · [Packing entry](https://github.com/google-deepmind/formal-conjectures/pull/4248) · [Left to Solve](https://www.lefttosolve.com/p/Erdos722.erdos_722) · [OMA reduction](https://github.com/lefttosolve2/open-math-agents/pull/17505) · [OMA rank-one entry](https://github.com/lefttosolve2/open-math-agents/pull/17952)

From the pinned Formal Conjectures checkout use `lake env python3 "$NOTEBOOK/scripts/replay-research" Erdos722BinaryOrbitEstimate`. [Replay instructions](../../README.md#replay)

Independent replay on Lean 4.33.1 covered all 40 modules in the import closure. A separate audit of all 111 public declarations in the 17 new modules found only `propext`, `Classical.choice` and `Quot.sound`. Fifteen comparisons checked the pinned host type, the finite-label conclusions, the class estimate and boundary cases. On the two-point base all switches are exceptional, illustrating the role of the cutoff.
