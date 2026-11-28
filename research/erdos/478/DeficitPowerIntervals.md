# Many factorial deficits in every power interval

Fix a positive integer $m$, a nonnegative integer $D$, and a real exponent $0<\alpha<1$. For **every sufficiently large integer** $X$, there are at least $X^\alpha$ primes $p$ such that
$$
X^\alpha<p\le X,\qquad p\equiv1\pmod m,\qquad
p-|A_p|\ge D,\qquad A_p=\{k!\bmod p:1\le k<p\}.
$$
For example, at least $\sqrt X$ primes in $(\sqrt X,X]$ are $1\bmod 12$ and miss at least six residues once $X$ is sufficiently large. The cutoff depends on $m,D,\alpha$. The theorem leaves it unspecified. [Factorial theorem and interval count](Erdos478DeficitPowerIntervals.lean)

The exponent can be arbitrarily close to one for each fixed $m,D$. The previous progression bound gave a degree-dependent exponent at arbitrarily large cutoffs. A separate unrestricted theorem gives a positive proportion of primes at arbitrarily large cutoffs. This result gives an ordinary count at every sufficiently large cutoff in the progression and permits removal of all primes up to $X^\alpha$. Whether the factorial image has density $1-1/e$ along all primes remains open. [Earlier progression count](SplittingFrequency.md) · [Earlier prime proportions](MeanDeficit.md) · [Pinned Erdős 478](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean)

## Why the interval contains so many primes

For a number field $K$, let $r_K(p)$ count the prime ideals of residue degree one above $p$. The main analytic lemma proves
$$
M_K(X)=\sum_{p\le X}r_K(p)\frac{\log p}{p}\sim\log X .
$$
The sum runs over rational primes. Fix $\alpha<\beta<1$. Subtracting the estimate at $\lfloor X^\beta\rfloor$ from the estimate at $X$ gives $(1-\beta+o(1))\log X$ of weight on $(X^\beta,X]$. Each prime contributes at most $[K:\mathbf Q]\log X/X^\beta$. Consequently at least a positive constant times $X^\beta$ primes in that interval have a degree-one prime above them. That bound eventually exceeds $X^\alpha$. [Degree-one Mertens estimate](Erdos478IdealPrimeWeights.lean)

Take $K$ to be the splitting field of the monic polynomial supplied by the notebook's factorial-gap and cyclotomic construction. Its roots are integral. A degree-one prime above $p$ has residue field of order $p$, so reducing those integral roots splits the polynomial over $\mathbf F_p$. Above the fixed bad-prime cutoff, the gap roots give distinct repeated factorial endpoints, and the cyclotomic roots force $m\mid p-1$. This gives `Erdos478.PowerIntervals.eventual_many_deficit_primes` for the exact finite factorial image in the pinned declaration. The same argument proves `splitting_primes_in_power_intervals` for every monic integer polynomial. [Gap construction](DisjointGapFamilies.md) · [Reduction and power intervals](Erdos478DeficitPowerIntervals.lean)

## Deriving the prime-ideal estimate

Let $A_K(y)$ count the nonzero integral ideals of norm at most $y$. Mathlib proves $A_K(y)/y\to c_K>0$. Multiplication by $\mathfrak p^j$ counts its multiples of norm at most $X$ by $A_K(X/N\mathfrak p^j)$. Unique ideal factorization therefore gives
$$
\sum_{N I\le X}\log N I
 = \sum_{\mathfrak p}\sum_{j\ge1} \log N\mathfrak p\; A_K(X/N\mathfrak p^j),
$$
where the outer index runs over nonzero prime ideals and $j$ runs over positive integers. On the left, summing $\log(X/N I)\le\sum_{N I\le n<X}1/n$ over the ideals costs $O_K(X)$. The left side is therefore asymptotic to $c_K X\log X$. [Log-norm convolution and estimate](Erdos478IdealMertens.lean) · [Mathlib ideal counting](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/NumberField/Ideal/Asymptotics.lean)

On the right, prime powers with $j\ge2$ and primes of residue degree at least two contribute $O_K(X)$ in total. The proof uses $\sum_p(\log p)/p^2<\infty$ and the bound $\sum_{\mathfrak p\mid p}f_{\mathfrak p}\le[K:\mathbf Q]$. In the remaining terms, replace $A_K(X/p)$ by $c_K X/p$. For every $\varepsilon>0$, the absolute error in $A_K(y)$ is at most $\varepsilon y+C_{K,\varepsilon}$ for all $y\ge0$. Chebyshev's bound for $\sum_{p\le X}\log p$ controls the additive error after summation. Letting $\varepsilon$ decrease gives $M_K(X)/\log X\to1$. [Prime-weight proof](Erdos478IdealPrimeWeights.lean)

## Prior work and replay

Garcia and Lee prove stronger explicit number-field Mertens estimates. Banks, Luca, Shparlinski and Stichtenoth establish a growing factorial deficit along infinitely many primes. Klurman and Munsch give quantitative ordinary-average bounds using factorial-gap polynomials and prime ideals. Classical Chebotarev gives positive density for complete splitting in the fixed Galois field. The Lean contribution here is the unconditionally checked interval count and its degree-one Mertens proof. The separate Chebotarev Lean project's general density declaration still contains an unfinished proof at the cited revision. [Garcia and Lee](https://arxiv.org/abs/2007.10313) · [Banks et al.](https://journals.tubitak.gov.tr/math/vol29/iss2/6/) · [Klurman and Munsch](https://www.numdam.org/articles/10.5802/jtnb.974/) · [Classical splitting density](https://math.stanford.edu/~conrad/676Page/handouts/dirdensity.pdf) · [Separate Lean declaration](https://github.com/cbirkbeck/chebotarev-density/blob/c64095e6cc6483b401849c7fd9182d983d3bf261/CebotarevDensity/Main.lean)

On 2026-11-28, the live LTS target had no submitted solution or active agent. The DeepMind PRs contained proposed statements. The OMA matches concerned a divisor-count statement and a reduction about factorial sums. A positive lower natural density in every such progression would strengthen the checked count. [LTS target](https://lefttosolve.com/p/Erdos478.erdos_478) · [DeepMind proposal](https://github.com/google-deepmind/formal-conjectures/pull/4078) · [DeepMind statement](https://github.com/google-deepmind/formal-conjectures/pull/5229) · [OMA divisor count](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7450) · [OMA factorial sum](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4056)

All six notebook modules passed a clean Lean 4.33.1 build with warnings as errors and independent kernel replay. The 34 printed declarations use only `propext`, `Classical.choice` and `Quot.sound`. [Notebook replay](../../README.md#replay)
