# Bounded mean squared error per prime

Let $E(p)=S(p)/p-(\log p)/2$, with $S$ the signed double floor sum in the pinned DeepMind file. There is an absolute constant $C>0$ such that, for every integer $X\ge2$,

```text
Σ_{p ≤ X, prime} E(p)² ≤ C X / log X.
```

Consequently the mean of $E(p)^2$ over the primes up to $X$ stays bounded. For every $t>0$, the number with $|E(p)|\ge t$ is at most $C X/(t^2\log X)$. For any prescribed fraction $\delta>0$, one fixed multiple of $p$ therefore bounds $|S(p)-(p/2)\log p|$ outside that fraction of the primes for all large $X$. The earlier stretched-exponential estimate remains stronger at large deviations such as $S(p)\le0$. [Finite sum, normalized mean and window count](ThetaPrimeVariance.lean) · [Previous large-deviation estimate](PRIME-CONCENTRATION.md)

For $F(p)=S(p)/(p\log p)-1/2$, the finite relative square sum is $O(X/\log^3 X)$. Its mean over primes is $O(1/\log^2 X)$, so the root mean square and the mean absolute relative error are both $O(1/\log X)$. All constants are existential. The bounds include $p=2$. The sign at every odd prime and eventual growth past each prescribed multiple of $p$ at every odd prime remain open. [Relative estimates](ThetaPrimeVariance.lean) · [Pinned definitions and conjectures](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean#L36-L95)

## Why the full logarithm is available

The previous second-moment estimate summed over all integer arguments and gave $O(X)$ on primes. To recover the factor $1/\log X$, split the previous cone interpolation by its original reduced denominator $d$. On the band $N^{56}\le p\le N^{64}$, the portion $d>N$ already has total squared norm $O(N^{64-1/64})$ even over all integer arguments. It remains to average the rows with $2\le d\le N$ over primes. Each row is extended by zero on arguments sharing a factor with $d$. [Denominator tail](ThetaDenominatorTails.lean) · [Row identity](ThetaRowCorrelations.lean)

For two rows write $d=gm$, $e=gn$, where $g=\gcd(d,e)$. On each residue class modulo $g$, the Chinese remainder theorem factors their product average over the coprime periods $m$ and $n$. For every primitive numerator, the sum of the signs on a fiber has magnitude at most the divisor count $\tau(m)$. Reflection and summation by parts preserve this gain over a reciprocal numerator window, with an extra factor $3H_d$, where $H_d$ is the harmonic number. The unweighted mean of the product is bounded by $9H_d H_e \tau(m)\tau(n)/(mn)$, uniformly in both window lengths. [Fiber estimate and covariance](ThetaRowCorrelations.lean) · [Complete-period factorization](ThetaPeriodMeans.lean)

Use the nonnegative square of a normalized sum of Ramanujan factors. For each squarefree $r\le N$, let $v_r(x)=\prod_{\ell\mid r}(1-\ell\,1_{\ell\mid x})$, where the product runs over primes. With $G=\sum_{r\le N,\,r\ \mathrm{squarefree}}1/\varphi(r)$, the weight is

```text
W(x) = (Σ_r v_r(x)/(φ(r) G))².
```

It equals one on primes above $N$. The local factors have mean zero and square mean $\ell-1$. Orthogonality on a complete period gives $W$ mean $1/G$, and the decomposition of every positive integer as a square times a squarefree integer gives $G\ge H_N/\zeta(2)$. Multiplication by a unit in a common period preserves $W$. Thus the weighted mean of two rows costs at most the absolute mean of the unweighted product times $1/G$ and $L/\varphi(L)$, where $L=\mathrm{lcm}(d,e)$. [Weight, orthogonality and normalizer](ThetaPrimeSieve.lean) · [Unit averaging](ThetaPeriodMeans.lean)

The elementary bound $L/\varphi(L)\ll L^{1/8}$ suffices. After the reciprocal row weights $1/(de)$, the absolute covariances including this unit-density factor are bounded by a constant times $g^{-3/2}m^{-9/8}n^{-9/8}$. The triple series converges, so the complete-period mean square is $O(1/G)$, uniformly in the cutoff and numerator windows. Expanding the sieve square and the row square before truncating the period gives an endpoint cost $O(N^{12})$ for bounded row coefficients. Each term now has period at most $N^4$. On a range of length $N^{64}+1$, this cost is absorbed into $O(N^{64}/\log N)$. The high-denominator estimate, Chebyshev’s bound for the prime count in the band, and the global Fourier estimate for the smaller primes complete the transfer to the original $S(p)$. [Uniform covariance sum](ThetaRowCorrelations.lean) · [Finite prime sieve](ThetaSievedWindows.lean) · [Transfer to all endpoints](ThetaPrimeVariance.lean)

## Scope and sources

Berndt, Bhat, Meyer, Xie and Zaharescu ask about the sign and pointwise growth of the aggregate. Lägeler studies distributions of phases of individual Hardy sums. Liu and Zhang study moments over numerators at fixed modulus. Weixia Liu’s short-interval theorem averages $H(2a\bar b,p)$ over pairs $(a,b)$ at fixed prime modulus. The results checked in the DeepMind issue, OMA and Left to Solve on 2026-11-28 yielded no matching prime-normalized second moment of the original signed aggregate. [Original paper, v3](https://arxiv.org/pdf/2501.03234v3#page=4) · [Lägeler](https://arxiv.org/abs/2207.04828) · [Liu and Zhang](https://ir.library.osaka-u.ac.jp/repo/ouka/all/10379/1658ojm.pdf) · [Weixia Liu, Theorem 1](https://www.emis.de/journals/AMAPN/vol28_1/28_01.pdf) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5611) · [LTS-listed harmonic lemma](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7126)

The scoped replay uses Lean 4.33.1, the pinned upstream definition and 23 local modules. The exported theorems report only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the derivation and formalization. [Notebook replay command](../../README.md)
