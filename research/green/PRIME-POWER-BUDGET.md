# Green 33 · Exact sums on prime powers

Let $X,Y$ be independent random variables on a common seed $A\subseteq\mathbb Z/p^e$, with $p$ prime. Suppose the atom probabilities of $X$ are rational. The probabilities of $Y$ may be arbitrary reals. The minimum possible $|A|$ for which $X+Y$ is uniform on the whole group is
\[
p^{\lfloor e/2\rfloor}+p^{\lceil e/2\rceil}-1.
\]
The exact threshold holds for every $e\ge0$. For $e=1$ it requires the entire prime group. For $e=2a+1$ the minimum is $(p+1)p^a-1$. Balanced radix digits attain the bound with both marginals rational. [`exact_budget_iff` and `radix_exact`](Green33PrimePowerBudget.lean)

For example, real weights on the four nonzero residues of $\mathbb Z/5$ already give a uniform sum. Put $a=(5+\sqrt5)/20$ and $b=(5-\sqrt5)/20$. Use masses $(a,b,b,a)$ and $(b,a,a,b)$ in the order $1,2,3,4$. The mass at zero is $4ab$, and the mass at every other residue is $a^2+ab+b^2$. Both equal $1/5$. The rational-marginal theorem requires five labels at this modulus. [`four_real_labels_mod_five`](Green33PrimePowerBudget.lean)

## Why the digit levels matter

Write $n=p^{d+1}$ and $t=p^d$. Let $T$ translate a function on $\mathbb Z/n$ by one, and let $F(X)=\sum_i f(i) X^i$ encode the rational marginal. Evaluating $F$ at $T$ gives convolution by $f$. The operator $D(T)=T^t-1$ annihilates any constant function. It also satisfies $D(T)\Phi_n(T)=0$, since $(X^t-1)\Phi_n(X)=X^n-1$. If $\Phi_n$ divides $F$ in $\mathbb Q[X]$, then $D(T)F(T)=0$, so $f$ is invariant under translation by $t$. Otherwise irreducibility gives a Bézout identity for $F$ and $\Phi_n$. When $F(T)g$ is constant, that identity gives $D(T)g=0$. Thus one of the two input functions is constant on the fibres of reduction to $\mathbb Z/t$. [`periodic_input`](Green33PrimePowerBudget.lean)

Project both marginals and repeat. At each of the $e$ levels, every atom in the periodic marginal has mass exactly $1/p$ of its parent’s mass. Every atom in the other marginal has mass at most its parent’s mass. Consequently there exist $r+s=e$ such that all the first marginal’s masses are at most $p^{-r}$ and all the second marginal’s masses are at most $p^{-s}$. The formal lemma also works for unnormalized nonnegative inputs. [`digit_caps`](Green33PrimePowerBudget.lean)

For atom masses $u_i,v_i$ on the common labels, exact uniformity gives $\sum_i u_iv_i\le p^{-e}$. This follows from the equality of sum and difference collision probabilities. An exactly uniform sum minimizes the collision probability, so the difference is also uniform. Equal labels contribute to its atom at zero. Now sum the pointwise inequalities $(1-p^r u_i)(1-p^s v_i)\ge0$. This gives $|A|+1\ge p^r+p^s$, whose minimum occurs when $r$ and $s$ differ by at most one. For the construction, if $n=tk$, take the fair digits $0,\dots,k-1$ and $0,k,\dots,(t-1)k$. They meet only at zero, and each residue has exactly one pair of digits. [Common-label proof](Green33PrimePowerBudget.lean) · [Sum and difference energy identity](WEIGHTED-SUM-PEAKS.md)

## Scope and sources

Ryazanov and Shankin study uniformity criteria on prime-power cyclic groups for inputs uniform on equal-size sets. Sherstnev gives criteria for uniform sums in finite abelian groups. The notebook uses cyclotomic irreducibility and the two-input collision identity to compute a common-support minimum when one input law is rational. [Ryazanov and Shankin (1997)](https://www.mathnet.ru/eng/dm458) · [Sherstnev (1998, English edition)](https://doi.org/10.1137/S0040585X97976957)

The pinned Green 33 declaration asks for full sumset coverage at asymptotic coefficient $\sqrt2$ on unbounded cyclic orders. Its weighted reformulation permits output distributions converging in total variation. The prime-power theorem assumes *exactly* uniform output. Green 33 stays open. The four-label example also distinguishes the rational-marginal scope from the prime-quotient bound for two unrestricted real marginals. Duplicate checks covered the DeepMind issue and formalization PR, Left to Solve, Open Math Agents and the personal notebook. [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Weighted equivalence](WEIGHTED-STABILITY.md) · [Prime quotients](PRIME-QUOTIENT-FLATNESS.md) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Formalization PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents/issues?q=%22Green33%22)

Replay `Green33PrimePowerBudget` with the [notebook runner](../../scripts/replay-research). A clean Lean 4.33.1 build and independent kernel replay cover seven notebook modules. All 62 axiom reports, including the six theorems in this file, use only `propext`, `Classical.choice` and `Quot.sound`.
