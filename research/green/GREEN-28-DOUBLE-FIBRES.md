# Green 28 with at most two representations through lighter atoms

Suppose the sum of two independent integer-valued random variables is uniform on its support. If one marginal has at most two distinct positive probabilities, its smaller-to-larger probability ratio has algebraic degree at most two, and every sum through a lighter atom has at most two representations, then both marginals are uniform. The other marginal may have arbitrarily many sites and probability values. Sums represented entirely through heavier atoms may have arbitrary multiplicity. If the first marginal has only one lighter site, the same conclusion holds in every algebraic degree. [Formal statements](Green28DoubleFibres.lean)

The Lean statements use the pinned predicates `Green28.indepSum` and `Green28.IsUniformOnSupport`. An ordered representation of $z$ consists of an occupied row $i$ of $P$ and column $z-i$ of $Q$. Finite support follows from the finite uniform output. Each rightmost atom attains its marginal's maximum probability, so dividing each marginal by its rightmost mass gives weights in $(0,1]$. A unique representation of the rightmost output fixes the total normalized mass of every occupied fibre at one. The source conjecture asks for the same conclusion for arbitrary marginals. [Pinned declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean) · [Normalized weights](Green28DeficientFibre.lean)

## A second lighter column

Fix a column of weight $u<1$ through which all sums have at most two representations. At any row of weight $w$, its contribution $uw<1$ needs a second cell. If that cell were always in a column of weight one, the map $w\mapsto1-uw$ would inject the finite set of distinct row weights into itself with $1$ removed. Thus some fibre joins two different lighter columns. Their weights generate the unit ideal in the ring generated over $\mathbb Z$ by all column weights. The two coefficients in the identity are the actual row weights at that fibre. This proves the one-lighter-site case. [Complementary cells and the unit ideal](Green28DoubleFibres.lean)

## Two positive mass values

Write $1,u$ for the column weights and $W$ for the finite set of row weights. For each $w\in W$, either $uw$ or $1-uw$ belongs to $W$. To see this, take the largest row of weight $w$ or $(1-uw)/u$, and the largest lighter column. A lighter partner in its fibre would have a row in the same row class and could increase neither coordinate. A heavier partner therefore supplies one of the two desired weights. The rightmost row and the largest lighter column also force $1-u\in W$. [Finite transition](Green28DoubleFibres.lean)

Choose one transition out of each row weight. Its image omits $1$, so two distinct weights $s,t$ collide. Such a collision has $u(s+t)=1$. As $s,t\le1$ and $s\ne t$, we get $u>1/2$. Monic division places all row weights in $\mathbb Z[u]$, so $u$ is a unit there. Specialization at zero gives $m(0)\mid1$ for its monic integral minimal polynomial $m$. [Monic division](Green28DeficientFibre.lean) · [Specialization](Green28NormOutcomes.lean)

For any conjugate $z$ and any rational polynomial $p$ with $p(u)\in W$, the same transitions act on the polynomial by $p\mapsto Xp$ or $p\mapsto1-Xp$. Some pair of states repeats at $u$ and hence at $z$. If $(|z|-1)|p(z)|>1$, successive absolute values would grow strictly because $|z||p(z)|\le1+|p_{\rm next}(z)|$. The seeds $1$ and $1-u$ yield
\[
 |z|\le2,\qquad (|z|-1)|1-z|\le1 .
\]
[Conjugate bound](Green28DoubleFibres.lean)

A rational algebraic integer cannot lie in $(1/2,1)$. In degree two the other conjugate $v$ has $uv=\pm1$ and $u+v\in\mathbb Z$. When $uv=1$, the trace lies strictly between two and three. When $uv=-1$, we have $v<-1$, and the second bound forces $v^2\le2$. The trace then lies strictly between $-1$ and zero. This excludes both possibilities. [Quadratic fairness theorem](Green28DoubleFibres.lean)

## Sources and replay

Ghidelli treated a specific three-site marginal via recurrences. Hare studied low-degree patterns, and a later trinomial manuscript treats all three-site marginals. The present assumptions constrain representation counts and mass values, with unrestricted support sizes. Live checks of the DeepMind issue and statement PR, Left to Solve and the OMA reductions found no matching theorem. The OMA two-site reduction counts support points. [Ghidelli](https://arxiv.org/abs/2209.09843) · [Hare](https://arxiv.org/abs/2307.07363) · [Trinomial manuscript](https://hexagonmath.org/pdf/2611.00674v2) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28) · [OMA R1](https://github.com/lefttosolve2/open-math-agents/pull/9606) · [OMA R2](https://github.com/lefttosolve2/open-math-agents/pull/21793) · [OMA two-site reduction](https://github.com/lefttosolve2/open-math-agents/pull/27234)

Rebuild `Green28DoubleFibres` with the notebook runner in the pinned Lake environment. The clean Lean 4.33.1 build and independent kernel replay covered twelve notebook modules. All 80 printed axiom reports used only `propext`, `Classical.choice` and `Quot.sound`. [Replay runner](../../scripts/replay-research)
