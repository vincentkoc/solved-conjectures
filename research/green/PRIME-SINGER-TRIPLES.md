# An unconditional gap for prime Singer lines

Let $p$ be prime and $v=p^2+p+1$. Let $D\subseteq\mathbb Z/v\mathbb Z$ be the projective labels of the kernel of a nonzero linear functional on a cubic extension of $\mathbb F_p$. For $p\ge10^6$, every full ordinary basis $T$ of the cyclic group of order $2v$ containing $2D$ satisfies
\[
             20000|T|\ge40001p,\qquad
             |T|/\sqrt{2v}\ge\sqrt2+10^{-5}.
\]
Both inequalities also hold with $|T|+|2D\setminus T|$ for every full basis, so deleting $o(p)$ points of the line still cannot achieve Green’s coefficient. Every balanced double $2D\cup(1+2B)$ with $|B|=p+1$ misses at least $p^2/20$ sums. The odd layer and additional even points of a full basis are arbitrary. These prime-field results are unconditional. The earlier proof assumes the pointwise rank-four Kloosterman bound and has a smaller numerical cutoff. Green 33 remains open for unrestricted bases. [Unconditional theorems](Green33PrimeSingerTriples.lean) · [Earlier conditional result](PRIME-SINGER-BASIS-GAP.md) · [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

## Counting triples on a Singer line

Every label $w$ has at least $p-80(\lfloor\sqrt p\rfloor+1)-8$ **ordered** three-term representations from $D$ when $p\ge400$. For primes $p\ge10000$ this lower bound is positive at every label, so $D+D+D$ covers the group. Repeated summands are allowed. The proof counts the finite parameters on a projective line and works for each $w$ individually. The constants are unoptimized. [Cyclic triple count](Green33PrimeSingerTriples.lean)

Choose two independent line points. After dividing by the first representative, the finite part of the line consists of $\theta-x$ for $x\in\mathbb F_p$, where $\theta$ has irreducible cubic minimal polynomial $m$. Write a representative of the normalized target as $u(\theta)$ with $\deg u\le2$. For $u(x)\ne0$, the cubic $u(x)m(Y)-m(x)u(Y)$ has the known root $x$. Write the residual quadratic as $u(x)Y^2+b(x)Y+c(x)$. Each root $y$ gives a third root $z=-b(x)/u(x)-y$ and the projective product
\[
   (\theta-x)(\theta-y)(\theta-z)=-\frac{m(x)}{u(x)}\,u(\theta).
\]
The scalar is nonzero. The discriminant $\Delta(x)=b(x)^2-4u(x)c(x)$ has degree at most four. Outside the at most two zeros of $u$, the number of choices of $y$ is $1+\chi(\Delta(x))$, with $\chi(0)=0$. Cubic rational maps and their splitting distributions also appear in the classification of permutation rational functions by Ferraguti and Micheli. [Fibre count and product identity](Green33SingerCubicFibers.lean) · [Ferraguti and Micheli](https://arxiv.org/abs/1805.03097)

If $\Delta$ has a geometric root of odd multiplicity, an elementary Stepanov auxiliary polynomial gives $|\sum_x\chi(\Delta(x))|\le80(\lfloor\sqrt p\rfloor+1)+4$. The two coefficient blocks have separated orders of vanishing at that root. Differentiating at the base-field points where the power has value one charges multiple roots to the degree of the auxiliary polynomial. This is a coarse bound from the classical Stepanov method. [Formal character bound](Green33PrimeQuarticCharacter.lean) · [Kopparty, *The Weil bounds*, §2](https://www.math.toronto.edu/swastik/courses/rutgers/finitefields-F13/weil.pdf) · [Cochrane and Pinner on the Stepanov–Schmidt method](https://www.math.ksu.edu/~cochrane/research/stepmix.pdf)

If every geometric root has even order, $\Delta$ is a scalar times a polynomial square over the base field. At the three distinct roots $\theta,s,t$ of $m$, the first value satisfies $\Delta(\theta)=(u(\theta)(s-t))^2\ne0$. A base-field scalar that becomes a square in an odd-degree extension is already a square, by taking norms. This case contributes a nonnegative character sum. Combining the two cases proves the triple bound without an estimate for any hyper-Kloosterman sum. [Odd-degree square witness](Green33PrimeQuarticCharacter.lean)

Summing the triple bound over the fourth point bounds all four-step path counts below. For the reflected double $R=2D\cup(1+2t-2D)$ and $H=2v-|R+R|$, the exact reflected-layer identity gives
\[
        p(p+1)\le4H+(p+1)\bigl(80(\lfloor\sqrt p\rfloor+1)+16\bigr).
\]
In particular $\liminf H/(2v)\ge1/8$, uniformly over axes. The earlier prime-plane stability and parity estimates then give the quadratic defect for every balanced opposite layer and the size gap for full bases. [Reflected count](Green33PerfectDifferenceCenters.lean) · [Prime-plane stability](Green33PrimeSingerIncidence.lean)

## Verification

Lean 4.33.1 rebuilt all 21 notebook modules in the dependency closure from source. Each module was replayed with the independent kernel checker. The 134 axiom reports use only `propext`, `Classical.choice` and `Quot.sound`. A separate elaboration compared the pinned DeepMind declaration by definitional equality and excluded its literal full-coverage and absolute-tolerance predicates at these positive cyclic orders.

A finite check compared the affine quadratic-root count with direct ordered multiplication for every projective label over primes 5, 7, 11, 17, 31 and 61. The two counts agreed on all 5,304 labels. At 61 their range was 42 through 116. Searches of the DeepMind, Open Math Agents and personal trackers located no matching implementation of the prime Singer triple estimate. Left to Solve listed no solution for the parent. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33)
