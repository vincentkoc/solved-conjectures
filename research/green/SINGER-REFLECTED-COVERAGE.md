# Coverage and repair of reflected binary Singer lines

For a finite field $F$ of characteristic two and order $q$, take a cubic field extension with a power basis $1,\theta,\theta^2$ and $\theta^3=p\theta+d$. Let $D\subset\mathbb Z/v\mathbb Z$, $v=q^2+q+1$, denote the projective labels of $F+F\theta$. For each $t\in\mathbb Z/v\mathbb Z$, put
\[
 B_t=\{2a:a\in D\}\ \cup\ \{1+2t-2a:a\in D\}\subset\mathbb Z/(2v)\mathbb Z.
\]
Then $|B_t|=2(q+1)$ and $|B_t+B_t|/(2v)\to 7/8$ as $q\to\infty$. The field, frame and axis may all vary. If $B_t\subset A$ and $A+A=\mathbb Z/(2v)\mathbb Z$, then
\[
 \liminf_{q\to\infty}\frac{|A|}{\sqrt{2v}}
       \ \ge\ \frac{3+\sqrt3}{2\sqrt2}.
\]
Lean states the lower bound as an eventual strict inequality for every smaller real number. The coefficient of $B_t$ itself tends to $\sqrt2$. Thus keeping all its points and repairing the holes cannot produce a family answering Green 33. The unrestricted problem remains open. [Coverage and repair theorems](Green33SingerReflectedCoverage.lean) · [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

## Exact count

Write $S=D+D$ and $I(c)=|S\cap(c-S)|$. The finite identity is
\[
             |B_t+B_t|+I(1+2t)+1=2v+2(q+1).
\]
To use it on the exact labels of the overlap theorem, we check their classical perfect-difference property in the same power basis. If $w=i+j\theta+k\theta^2$ is nonscalar, the coefficient of $\theta^2$ in $w(a+b\theta)$ is $ka+jb$. Its zero directions form the single projective point $(a:b)=(j:k)$. Thus each nonidentity projective multiplier sends precisely one line point back into the line. This gives one ordered representation of every nonzero cyclic difference, and the parameter identity gives $|D|=q+1$. The two layers lie in opposite parity classes. [Coordinate proof](Green33SingerReflectedCoverage.lean) · [Finite doubled count](Green33PerfectDifferenceCenters.lean) · [Singer’s theorem](https://doi.org/10.1090/S0002-9947-1938-1501951-4)

The earlier all-center theorem gives $I(1+2t)/v\to1/4$. Substitution in the finite identity gives the coverage limit. The notebook's Sidon extension estimate, applied to this overlap and $|D|/\sqrt v\to1$, gives the lower bound for arbitrary full supersets. The formal hypotheses on the frame are the cubic relation and the power-basis bijection. [Quarter-overlap theorem](Green33SingerProjectiveOverlap.lean) · [Sidon repair inequality](Green33SidonLayerRepairs.lean) · [Earlier formalization of the prime-power Singer construction](https://github.com/d0d1/singer-theorem-lean/blob/0c890589afc58e8955a5d7c3a609daff6447da31/Erdos30/SingerPrimePowerTheorem.lean)

## Verification

The independent Lean 4.33.1 replay rebuilt and kernel-checked 11 notebook modules. The 89 axiom reports across the dependency closure use only standard Lean axioms. A separate comparison with the pinned Green 33 type applied its literal full-coverage and size predicates to supersets of these layers. Direct enumeration at $q=2,4,8,16$ checked all 374 axes against the layer cardinality and the finite coverage identity. DeepMind and Open Math Agents tracker searches returned no matching reflected Singer result. Left to Solve listed Green 33 as open. [Earlier overlap PR](https://github.com/vincentkoc/solved-conjectures/pull/374) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33)
