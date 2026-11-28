# Exact Cunningham pairs at growing gaps

For a natural cutoff $N$, let $W(N,H)$ count pairs of seeds $a<b\le N$ with an exact first-kind chain of length one at $a$ and an exact second-kind chain of length one at $b$. Give a pair of gap $g=b-a$ weight $\max(0,H-g)$. Thus a contribution requires $a$ and $b$ prime and both $2a+1$ and $2b-1$ nonprime.

If $H=H(N)$ satisfies $H/N\to0$ and $H/\log N\to\infty$, then unconditionally
$$
\liminf_{N\to\infty}\frac{2N\,W(N,H)}{H^2\pi(N)^2}\ \ge\ 1.
$$
More generally, $H\pi(N)/N\to\infty$ suffices in place of the logarithmic condition. The Lean statement says that every constant less than one eventually lies below the displayed ratio. It permits arbitrary natural cutoff functions satisfying the two limits. [Asymptotic theorem](CunninghamMesoscopicPairs.lean) · [Canonical chain predicates](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean)

This is a joint limit for a growing range of gaps. For instance, $H=\lfloor\sqrt N\rfloor$ satisfies the two hypotheses. It gives a lower bound for the weighted sum of observed pairs. Counts at any fixed gap and matching upper asymptotics remain open in general. The [earlier Euler-product average](MeanPairedExactCounts.md) includes all positive chain lengths and identifies the coefficient of the fixed-gap counts under Bateman–Horn, before averaging over gaps.

## A finite inequality

Write $T(N)$ for the number of seeds at most $N$ having exact length one **for both signs**. For all natural $N,H$, including empty windows,
$$
 (H T(N))^2\le(N+H)\bigl(H T(N)+2W(N,H)\bigr).
$$
To see the weight $H-g$, place an interval of $H$ integer points at each seed with both stops. For each position $j$ let $c_j$ be the number of these intervals containing it. Then $\sum c_j=HT$, and $\sum c_j^2$ counts the diagonal contributions $HT$ plus twice the overlaps of distinct seed intervals. Two intervals whose seeds differ by $g$ overlap in exactly $\max(0,H-g)$ positions. Cauchy–Schwarz on the $N+H$ possible positions gives the inequality. Enlarging the left set of seeds to all exact first-kind singletons and the right set to all exact second-kind singletons preserves the lower bound. [Finite window inequality](CunninghamGapClosePairs.lean) · [Application to the exact predicates](CunninghamSingletonPairWindows.lean)

Almost every prime seed has length exactly one for each sign by the earlier sieve bound. Inclusion–exclusion gives $T(N)/\pi(N)\to1$. In the finite inequality the diagonal correction vanishes after normalization when $H$ grows faster than $N/\pi(N)$, and the endpoint factor $N/(N+H)$ tends to one. Chebyshev’s lower bound for $\pi(N)$ yields the logarithmic formulation. [Single-seed sieve estimate](CunninghamSelbergSieve.lean) · [Jones](https://arxiv.org/abs/1104.1579)

A separate enumeration checked the two window identities and the finite inequality for 101 finite sets with varying cutoffs. Directly testing the primality of each seed and its two successors gave the following opposite-kind pair weights.

| Seed bound $N$ | Gap cutoff $H$ | Seeds with both stops | $W(N,H)$ |
| --- | --- | --- | --- |
| 100 | 12 | 9 | 134 |
| 1,000 | 60 | 98 | 28,242 |
| 10,000 | 220 | 852 | 2,538,144 |

Live searches of the DeepMind and Open Math Agents issues and pull requests and 12,550 Left to Solve records found the Jones statement and existing reductions. No matching weighted pair theorem appeared. This is a formalization of an elementary second-moment argument. Codex assisted with the proof. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/4755) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/4770) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents) · [Left to Solve](https://lefttosolve.com/api/solved)

A fresh Lean 4.33.1 build and independent kernel replay checked 5 notebook modules. All 19 named axiom reports used only `propext`, `Classical.choice` and `Quot.sound`. The six named theorems in the three new modules each have an axiom report. Run the focused notebook replay with `CunninghamMesoscopicPairs`. [Replay instructions](../../README.md#replay)
