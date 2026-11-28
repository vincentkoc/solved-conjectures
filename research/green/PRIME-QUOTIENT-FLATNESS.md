# Green 33 · Exact uniform sums on prime quotients

Let $A\subseteq\mathbb Z/M$, and let $X,Y$ be independent random variables on $A$ with arbitrary probability weights. If $X+Y$ is exactly uniform and $p\mid M$ is prime, then
\[
p+1\leq |\operatorname{supp}(X\bmod p)|+|\operatorname{supp}(Y\bmod p)|\leq 2|A|.
\]
The first inequality holds for every surjective homomorphism from a finite abelian group onto $\mathbb Z/p$. It counts a site twice when both projected laws occupy it. [`quotient_support` and `prime_divisor_budget`](Green33PrimeFlatness.lean)

For prime $M$, this gives a linear lower bound on the common seed size. By comparison, the notebook constructs on *every* modulus a sum on at most $2\lfloor\sqrt M\rfloor-1$ common labels with total-variation error at most $1-\lfloor\sqrt M\rfloor^2/M$. Thus allowing a vanishing error changes the support requirement even along primes. DeepMind’s pinned Green 33 declaration asks for full sumset coverage at the $\sqrt2$ coefficient along unbounded moduli. Its weighted reformulation asks for convergence in total variation. The exact-uniform obstruction leaves both existence questions open. [Every-order radix construction](WEIGHTED-SUM-PEAKS.md) · [Weighted equivalence](WEIGHTED-STABILITY.md) · [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

## Support inequality and attribution

For any field $K$ of characteristic zero, take nonzero $f,g:\mathbb Z/p\to K$ whose cyclic convolution is constant $c$. The formal bound is
\[
 |\operatorname{supp} f|+|\operatorname{supp} g|\geq
 \begin{cases}p+1 & c\ne 0,\\ p+2 & c=0.\end{cases}
\]
Over $\mathbb C$ the inequality is a consequence of the published prime Fourier uncertainty principle. Each input and its Fourier transform occupy at least $p+1$ sites in total. The two Fourier supports intersect in at most the trivial frequency for constant convolution and are disjoint for zero convolution. Chebotarev’s nonvanishing Fourier minors underlie that uncertainty theorem. The first numerical bound is attained by a constant input and a point mass. For the zero case, take a constant input and the difference of two distinct point masses. These examples concern total support counted with multiplicity. [`constant_support`](Green33PrimeFlatness.lean) · [Tao, *An uncertainty principle for cyclic groups of prime order*](https://arxiv.org/abs/math/0308286) · [Frenkel, *Simple proof of Chebotarev’s theorem on roots of unity*](https://arxiv.org/abs/math/0312398) · [Sherstnev on uniform sums in finite abelian groups](https://doi.org/10.1137/S0040585X97976957)

## Formal argument

1. Over a field of characteristic $p$, a nonzero input on $s$ distinct sites has a nonzero moment $M_j(f)=\sum_x f(x)x^j$ with $j<s$. Multiplication by $x-a$ removes a chosen site $a$. Induction on the sites gives the claim.
2. Let $j,k$ be the first nonzero moment indices of the two inputs. If $j+k<p$, the convolution moment of degree $j+k$ is $\binom{j+k}{j}M_j(f)M_k(g)\ne0$. All other terms of the binomial expansion vanish. A constant function has zero moments through degree $p-2$ in characteristic $p$. The zero function has all moments zero. This yields the two bounds.
3. In characteristic zero, choose a valuation ring over the prime ideal $(p)$ of the integers. Divide each input by a coefficient of maximal valuation before reducing to its residue field. Each reduced input has a coefficient equal to one, neither support grows, and constant convolution stays constant. A zero convolution stays zero.
4. A uniform law projects to a constant law on a prime quotient because translation identifies its fibres. Pushing the two marginals forward commutes with taking their independent sum. Applying the characteristic-zero theorem to their real atom masses gives the stated probability bounds. [Lean proof](Green33PrimeFlatness.lean)

The source check included DeepMind’s issue and formalization PR, the Left to Solve problem page, Open Math Agents and the personal notebook. Searches covered prime uncertainty and the weighted prime-quotient statement. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Formalization PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents/issues?q=%22prime+uncertainty%22)

Replay `Green33PrimeFlatness` with the [notebook runner](../../scripts/replay-research). An independent Lean 4.33.1 kernel replay covers six notebook modules and 45 axiom reports, including all three public theorems above. Each report lists only `propext`, `Classical.choice` and `Quot.sound`.
