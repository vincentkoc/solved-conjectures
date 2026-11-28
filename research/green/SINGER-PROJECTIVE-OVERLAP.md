# Reflection of a binary Singer sumset

Let $F$ have order $q$ and characteristic two. In a cubic extension $K$, fix a basis $1,\theta,\theta^2$ with $\theta^3=p\theta+d$. Take the nonzero elements of the line $F+F\theta$, quotient by $F^\times$, and write their labels as $D$ in the cyclic group of order $v=q^2+q+1$. Write $S=D+D$, with repeated summands allowed. For **every** sequence of centers $c$ and frames as $q\to\infty$,
\[
              \frac{|S\cap(c-S)|}{v}\longrightarrow\frac14 .
\]
This includes the identity center. It excludes sublinear overlap throughout this construction class, a necessary condition from the notebook for reflected pairs of perfect difference sets to cover nearly all residues. The cyclic labels and their ordinary sumset are constructed in Lean. The input frame supplies the cubic relation and power-basis bijection. Green 33 allows arbitrary cyclic sets and asks for full coverage at size coefficient $\sqrt2$. It remains open. [Cyclic limit](Green33SingerProjectiveOverlap.lean) · [Earlier reflected-layer criterion](Green33PerfectDifferenceCenters.lean) · [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

## Finite estimate and exact descent

Let $M=(F+F\theta)(F+F\theta)\subset K$, let $w\in K^\times$ represent $c$, and let $H$ count $z\in M$ for which $w/z\in M$, including the origin under Lean's totalized division. If $R(q)=(15q^7)^{1/8}$, then
\[
  |4H-q^3|\le q^2(R(q)+13),\qquad
  H=1+(q-1)|S\cap(c-S)|.
\]
The single extra point is the origin. All other points come in scalar orbits of size $q-1$. The bound and the count hold before taking any limit. [Field estimate](Green33SingerCoordinates.lean) · [Exact orbit count](Green33SingerProjectiveOverlap.lean)

The form $aX^2+bXY+cY^2$ splits precisely when the element $a+b\theta+c\theta^2$ is a product from the line. On the chart $b=1$, the coordinates of $w/z$, up to a nonzero scalar, are three plane quadratics. The discriminant of the middle conic equals $d$ times the cubic norm of $w$. Both factors are nonzero. This establishes the nonsingularity needed at every center. On each regular line in a pencil, the phase comparison reduces to correlation of inversion with a quadratic Boolean phase. Three applications of Cauchy–Schwarz and an explicit count of additive cubes give the bound $R(q)$. The pencil estimate handles exceptional slopes, poles and the missing projective chart. [Reciprocal character sums](Green33ReciprocalCharts.lean) · [Splitting signs and pencils](Green33SplitPencils.lean) · [Discriminant and norm](Green33SingerCoordinates.lean)

## Sources and verification

Singer constructed the cyclic projective-plane difference sets. Hulak, Ramos and de Queiroz formalized Singer’s construction for every prime power, starting with the prime-field presentation. Carlet studied quadratic approximation of field inversion. Tang, Mandal and Maitra treated its Gowers $U^3$ norm. The elementary estimate here is used for the reflected projective sumset. No priority claim is made for the analytic bound or the overlap asymptotic. [Singer](https://doi.org/10.1090/S0002-9947-1938-1501951-4) · [Singer formalization paper](https://arxiv.org/abs/2605.03274) · [Prime-power Lean theorem](https://github.com/d0d1/singer-theorem-lean/blob/0c890589afc58e8955a5d7c3a609daff6447da31/Erdos30/SingerPrimePowerTheorem.lean) · [Carlet](https://eprint.iacr.org/2006/459) · [Tang, Mandal and Maitra](https://eprint.iacr.org/2020/920)

Four modules were elaborated from clean sources using Lean 4.33.1 and replayed separately with the independent kernel checker. All 29 axiom reports contain only standard Lean axioms. A separate type check compared the pinned Green 33 declaration by definitional equality and specialized the cyclic limit to its literal full-sumset predicate. A separate finite-field enumeration verified the norm/discriminant identity and the exact orbit count at all 374 centers for $q=2,4,8,16$. The minimum and maximum cyclic overlaps were $5,6$ at order 7, $9,13$ at order 21, $23,36$ at order 73, and $77,99$ at order 273.

The live DeepMind and Open Math Agents issue/PR searches for Singer reflections, Singer overlaps and reciprocal Gowers bounds found no matching entry. The personal tracker returned the earlier perfect-difference-set obstruction, which leaves the zero-center case open in its wider class. Left to Solve listed the source problem as open. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33) · [Earlier center obstruction](https://github.com/vincentkoc/solved-conjectures/pull/369)
