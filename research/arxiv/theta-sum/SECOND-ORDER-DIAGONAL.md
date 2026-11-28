# The prime theta sum crosses its leading term in both directions

The original integer sum $S(p)$ satisfies each of the following inequalities on a set of positive upper density relative to **all** primes.

| Prime progression | Excursion from the leading term |
| --- | --- |
| $p\equiv1\pmod{24}$ | $S(p)>\tfrac12p\log p+\tfrac{13}{50}p$ |
| $p\equiv17\pmod{24}$ | $S(p)<\tfrac12p\log p-\tfrac1{1000}p$ |

For each row there exists $\delta>0$ such that at least $\delta\pi(X)$ primes satisfy the inequality at arbitrarily large endpoints $X$. The two sets of endpoints can differ. Both progressions are $1\bmod8$. Consequently, $\tfrac12p\log p$ crosses the original sum with fluctuations of order at least $p$ in both directions. [Original-sum theorem](ThetaHalfLogExcursions.lean)

## The second coefficient

Let $D(p)$ be the exact divisible cotangent diagonal of the theta sum. Along **all positive integers** tending to infinity,
\[
  \frac{D(p)}p-\tfrac12\log p\longrightarrow B,\qquad
  B=\frac12\log(2/\pi)+\frac{4}{\pi^2}
    \sum_{\substack{u\ge1\\u\ {\rm odd}}}\frac{\gamma+\log2-\log u}{u^2}.
\]
Here $\gamma$ is Euler’s constant. The convergent series gives $B\approx0.2399341$ numerically. Lean proves $0<B<259/1000$. The Lean declaration uses $u=2j+1$. [Second-order theorem](ThetaDiagonalConstant.lean) · [Exact diagonal](ThetaDivisibleDiagonal.lean)

For every real $c<32/(15\pi^2)$, each row below holds on a set of positive upper density relative to **all** primes. The endpoints realizing the two densities may differ.

| Prime progression | Normalized original sum |
| --- | --- |
| $p\equiv1\pmod{24}$ | $S(p)/p-\tfrac12\log p>B+c$ |
| $p\equiv17\pmod{24}$ | $S(p)/p-\tfrac12\log p<B-c$ |

In particular, for **every** proposed second coefficient $a$ and $0<c<32/(15\pi^2)$, a positive upper density of all primes satisfy both $p\equiv1\bmod8$ and $|S(p)/p-\tfrac12\log p-a|>c$. This rules out concentration of the normalized residual at any single constant, even within that congruence class. The argument transfers the earlier excursions by discarding finitely many initial primes and spending an arbitrarily small margin in the threshold. The all-prime positivity conjecture remains open. [Prime theorems](ThetaDiagonalConstant.lean) · [Excursions about the exact diagonal](OFF-DIAGONAL-EXCURSIONS.md)

## Certifying the signs

The finite model at every admissible frozen cutoff includes the odd common factors $1,3,\ldots,21$ in its denominator-three coefficient. Their inverse squares sum to more than $121/100$. Keeping this weight in the signed class mean raises the provable threshold for $|S(p)-D(p)|/p$ above $13/50$. The certified bounds $0<B<259/1000$ then give the two strict inequalities in the first table. [Weight-sensitive transfer](ThetaOffDiagonalSigns.lean) · [Explicit comparison](ThetaHalfLogExcursions.lean)

To enclose $B$, put $M=\sum_{u\ \mathrm{odd}\ge1}(\log u)/u^2$. Summing odd inverse squares gives $B=(\gamma+\log(4/\pi))/2-4M/\pi^2$. For the lower bound on $M$, take $k=\lfloor\log_2u\rfloor$ and $b=2^k$. The inequality $\log(1+x)\ge2x/(2+x)$ gives
\[
  \log u\ge k\frac{69314}{100000}+\frac{2(u-b)}{u+b}.
\]
The first 128 odd terms already give a rational lower bound above $403/1000$. The upper bound $M\le78/100$ follows by bounding the tail with differences of reciprocal square roots. An upper estimate for $\gamma$ uses $H_{64}-\log64$. The finite rational comparisons use Lean kernel evaluation. [Certified enclosure](ThetaCenterBounds.lean)

## Computing the constant

For each fixed odd $u$ put $y=\pi u/(2p)$, and let $m$ count the positive odd multiples of $u$ below $p$. The odd harmonic sum $H_o(m)=H_{2m}-H_m/2$ supplies the limiting contribution $(\gamma+\log2-\log u)/2$ after subtracting $\tfrac12\log p$. The centered terms have a summable bound independent of $p$. [Harmonic limit and domination](ThetaDivisibleDiagonal.lean) · [Fixed-row limit](ThetaDiagonalConstant.lean)

For the cotangent correction put $g(x)=\cot x-1/x$. On $(0,\pi)$, $g$ is the derivative of $\log(\sin x/x)$ and is decreasing since $\sin x\le x$. On each interval of length $2y$, the mean value theorem places the increment of the logarithm between the endpoint derivative bounds. The error of the midpoint sum is bounded by $2y$ times the total drop in $g$. Since $2my\to\pi/2$, it follows that
\[
  2y\sum_{k<m}g((2k+1)y)\longrightarrow \log(2/\pi).
\]
The existing pointwise product bound controls the outer cotangent factor. The resulting correction for a fixed $u$ is $4\log(2/\pi)/(\pi^2u^2)$, dominated in absolute value by $2/u^2$ before passing to the limit. Summing over odd $u$ gives $\tfrac12\log(2/\pi)$. [Midpoint theorem](ThetaCotangentMidpoints.lean) · [Cotangent row and full diagonal](ThetaDiagonalConstant.lean)

OMA’s reduction of $p<S(p)$ uses a finite range and a separate implication above its cutoff. A different PR checks the finite range $3119<p<100000$ for the $3p$ inequality. [OMA harmonic reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/21155) · [OMA finite verification](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18042)

The prime statements use the pinned integer-valued $S$ and the unconditional diagonal decomposition at odd primes. The paper conjectures pointwise lower bounds for $S(p)$. DeepMind’s open issue reduces those bounds to a remainder, and the LTS-listed harmonic lemma supplies a lower estimate for an uncentered harmonic sum. [Original paper](https://arxiv.org/abs/2501.03234) · [Pinned definitions and conjectures](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean) · [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [LTS-listed proof](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7126)

Codex assisted with the derivation and Lean formalization. [Notebook replay](../../README.md)
