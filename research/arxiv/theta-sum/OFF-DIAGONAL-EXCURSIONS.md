# Signed prime excursions around the divisible theta diagonal

Write $D(p)$ for the exact cotangent contribution of odd pairs $(u,v)$ with $u\mid v$ in the decomposition of the original integer sum $S(p)$. For every $0<c<32/(15\pi^2)$, each of the following sets has positive upper density relative to **all** primes.

| Prime progression | Excursion |
| --- | --- |
| $p\equiv1\pmod{24}$ | $S(p)-D(p)>cp$ |
| $p\equiv17\pmod{24}$ | $S(p)-D(p)<-cp$ |

Precisely, for each row there exists $\delta>0$ such that its prime count through $X$ is at least $\delta\pi(X)$ for arbitrarily large $X$. The endpoints and $\delta$ may differ between the rows. Both progressions lie in $1\bmod 8$. The Lean statement admits every real $c<32/(15\pi^2)$. [Original-sum theorem](ThetaOffDiagonalSigns.lean) · [Exact diagonal](ThetaDivisibleDiagonal.lean)

The subsequent [second-order theorem](SECOND-ORDER-DIAGONAL.md) computes the linear coefficient of the diagonal and transfers the excursions to the explicit center $p\log p/2$.

## Transfer from finite windows

Put $R(p)=(\pi^2/8)(S(p)-D(p))/p$ at odd primes. For each $\eta>0$ there is a single periodic reciprocal-row model $F$, with both truncation parameters fixed, for which
\[
  \sum_{p\le X,\ p\ {\rm prime}} |R(p)-F(p)|^2 \le \eta\,\pi(X)
\]
for all sufficiently large $X$. In Lean the sum includes $2$ using the everywhere-defined off-diagonal. Cauchy–Schwarz gives the corresponding approximation in mean absolute error. [Approximation theorems](ThetaPrimeTailTransfer.lean)

The factors $d^{1/16}e^{1/16}$ preserve summability of the row-correlation majorant. In the parametrization $d=gm,\ e=gn$, the three exponents after weighting are $11/8,17/16,17/16$. Restricting to denominators greater than $T$ then buys $T^{-1/8}$ in the sieved second moment. The earlier high-denominator estimate treats $d>N$ on the prime scale $N^{56}\le p\le N^{64}$. For the finitely many retained rows, bounded reciprocal partial sums give convergence of the harmonic numerator windows, uniformly over a finite period. Rounding an arbitrary endpoint up to the next 64th power and using the lower prime-count estimate gives the stated normalization. [Correlation bounds](ThetaRowCorrelations.lean) · [Sieved denominator tail](ThetaSievedWindows.lean) · [Prime-scale estimates](ThetaPrimeTailTransfer.lean)

The fixed model has reduced-residue mean at least $1/30$ after multiplication by the indicator of $1\bmod 24$. The mean with the indicator of $17\bmod 24$ is at most $-1/30$. Either class has mass $1/8$. For the corresponding sign $s$ and any $b<4/15$, the periodic test $\mathbf1_r(sF-b)-2\varepsilon$ therefore has positive mean when $\varepsilon$ is sufficiently small. Its ordinary prime partial sums are unbounded above by Abel summation of the progression prime series. At endpoints with positive test sum, discrepancies between $F$ and $R$ absorb at most $\varepsilon\pi(X)$. Boundedness of the fixed model forces a positive fraction of the primes to satisfy $sR>b$. Multiplication by $8/\pi^2$ gives the threshold in the table. [Reduced-residue means](ThetaConditionalRows.lean) · [Abel summation](ThetaAbelPrimes.lean) · [Prime-count argument](ThetaOffDiagonalSigns.lean)

## Scope and related work

The proof uses the pinned $S$ itself and the unconditional equality $S(p)=D(p)+\mathrm{offDiagonal}(p)$ at odd primes. The center satisfies $D(p)=\tfrac12 p\log p+O(p)$. The universal positivity and lower bounds in the upstream declarations remain open. The negative excursion is a statement about the difference $S(p)-D(p)$. [Pinned declarations](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean) · [Berndt, Bhat, Meyer, Xie and Zaharescu](https://arxiv.org/abs/2501.03234) · [Previous fixed-cone theorem](RESIDUE-CLASS-BIAS.md)

DeepMind issue 7589 gives row identities and a reduction to a remainder. OMA's finite verification concerns $3p<S(p)$ for $3119<p<100000$. The matching LTS solved record supplies an odd-harmonic lemma. Lägeler studies the distribution of individual Hardy sums. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA finite verification](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18042) · [LTS-listed lemma](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7126) · [Lägeler](https://arxiv.org/abs/2207.04828)

The independent replay uses Lean 4.33.1 and the pinned upstream source. Codex assisted with the argument and formalization. [Notebook replay](../../README.md)
