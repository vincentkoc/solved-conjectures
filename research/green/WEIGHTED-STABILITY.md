# Green 33 · Weighted near-uniform sums

Green 33 is equivalent to the existence of cyclic groups of orders $M\to\infty$, sets $A\subseteq\mathbb Z/M$ with $|A|\le(\sqrt2+o(1))\sqrt M$, and independent draws $X,Y$ from $A$ whose sum approaches uniform on the whole group in total variation. The two input laws may differ and may assign zero mass to labels. Every such sequence satisfies
\[
\frac{|A|}{\sqrt M}\longrightarrow\sqrt2,\qquad
d_{\rm TV}(\mathcal L(X),U_A)\longrightarrow0,\qquad
d_{\rm TV}(\mathcal L(Y),U_A)\longrightarrow0 .
\]
Here $U_A$ gives every label in the common budget the same mass. The limits hold uniformly over all events, even when the event varies with the modulus. The existence of these sequences remains Green's open question. [Equivalence and marginal limits](Green33WeightedStability.lean) · [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

## Finite bound

Take two independent laws $P,Q$ on $n$ labels and any symmetric observation $f(i,j)=f(j,i)$. Assume that each event $E$ has observation probability at most $|E|/m+\delta$. On a finite observation space of size $m$ this is equivalent to total variation at most $\delta$ from uniform. Choose $0\le t\le1$ with $t n(n+1)\le2m$ and put $e=1-t(1-\delta)$. For any label subset $T$, write $a=P(T)$, $b=Q(T)$ and $x=|T|/n$. Then
\[
\left|\frac{a+b}{2}-x\right|\le e,\qquad (a-b)^2\le6e,\qquad
\max(|a-x|,|b-x|)\le e+\sqrt{3e/2}.
\]
For identically distributed draws the first bound already gives $d_{\rm TV}(P,U_A)\le e$. [`weighted_stability` and `diffuse_iff_tv`](Green33WeightedStability.lean)

The count includes diagonal pairs once. For $k=|T|$, two draws in $T$ give at most $k(k+1)/2$ observations. Exactly one draw in $T$ gives at most $k(n-k)$ because the observation is symmetric. Adding the bounds for both draws in $T$ and at least one in $T$ gives $m(a+b-2\delta)\le k(n+1)$. Applying the same bound to the complement controls the average of $a,b$ from both directions. The probability of exactly one draw in $T$ is $2y(1-y)+(a-b)^2/2$, where $y=(a+b)/2$. The cross-pair count therefore controls the separation of the two laws. [Finite counting argument](Green33WeightedStability.lean)

## From weights to a basis and back

The observation $X+Y$ belongs to $A+A$ with probability one. Thus at most $\delta M$ residues can be missing. The all-label count also gives $2M(1-\delta)\le |A|(|A|+1)$, which forces the size ratio to converge under the given upper budget. The notebook's approximate-cover theorem then gives the original Green 33 statement. In the other direction its strict-cover reduction supplies optimal-size seeds where each residue has two distinct ordered representatives. Fair independent draws give each residue probability at least $2/|A|^2$, hence total variation at most $1-2M/|A|^2\to0$. [Approximate covers](APPROXIMATE-COVERS.md) · [Strict-cover reduction](STRICT-REDUCTION.md) · [Weighted proof](Green33WeightedStability.lean)

The left side of `green_iff_weighted` is the type of the pinned `Green33.green_33` declaration, including its frequent positive moduli, full ordinary cover, and absolute error in the size ratio. The DeepMind issue and statement PR, Left to Solve, Open Math Agents and this notebook were checked for a matching weighted criterion. The existing approximate-cover result supplies the repair step. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33) · [Open Math Agents search](https://github.com/lefttosolve2/open-math-agents/issues?q=%22Green33%22)

All five notebook modules passed an independent Lean 4.33.1 kernel replay after rebuilding from source. All 42 axiom reports, including the seven declarations printed in this module, contain only `propext`, `Classical.choice`, and `Quot.sound`. Replay `Green33WeightedStability` with the [notebook runner](../../scripts/replay-research).
