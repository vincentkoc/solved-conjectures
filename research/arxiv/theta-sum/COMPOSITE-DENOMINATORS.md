# Negative theta sums on composite denominators

For the original integer sum $S$ of Berndt, Bhat, Meyer, Xie and Zaharescu, let $a>1$ be any fixed odd integer with $r=\omega(a)\ge3$ distinct prime factors. Then
\[
 \lim_{n\to\infty}\frac{S(a^n)}{a^n n^r}
   =-\frac12\prod_{p\mid a,\ p\ {\rm prime}}v_p(a)\left(1-\frac1p\right)<0.
\]
In particular $S(a^n)/a^n\to-\infty$. For $a=105=3\cdot5\cdot7$ the limit in the display is $-8/35$. This proves the authors’ suggestion in §3 that $S(k)/k$ can be arbitrarily negative at composite denominators. The pinned DeepMind positivity conjecture concerns prime denominators and remains open. [Unconditional Lean limits](ThetaCompositePowers.lean) · [Paper, §3, p. 6](https://arxiv.org/pdf/2501.03234v3#page=6) · [Published article](https://doi.org/10.1007/s00025-025-02584-2) · [Canonical definitions and prime hypotheses](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean#L41-L95)

The same unbounded negativity holds on squarefree denominators. Let $P_n$ be the product of the first $n$ odd primes, and let $G(k)=\sum_{j=1}^k\gcd(j,k)$. Then $S(P_n)/G(P_n)\to-1/2$ and $S(P_n)/P_n\to-\infty$. In this family each prime occurs just once. [Squarefree primorial limits](ThetaOddPrimorial.lean)

The estimate before taking a limit is uniform over all positive odd $k$. Write $m=(k-1)/2$, $H_m=\sum_{j=1}^m 1/j$, and let $G$ denote Pillai’s gcd sum above. Then
\[
 \left|kS(k)+m\bigl(G(k)-k\bigr)\right|\le 4(kH_m)^2.
\]
When $k$ is prime, $G(k)-k=k-1$ and this specializes to the earlier centered prime estimate. For composite $k$, Berndt et al. already give the exact formula $T(k)=2k-1-2G(k)$ for their separate complete sum $T$. Substitution now gives $|S(k)-(k-1)(T(k)+1)/(4k)|\le4kH_m^2$. [Uniform estimate](ThetaCompositeFourier.lean) · [Earlier prime bound](FOURIER.md) · [Paper, Lemma 4.1](https://arxiv.org/pdf/2501.03234v3#page=6) · [Classical gcd-sum identities, equations (1)–(3)](https://cs.uwaterloo.ca/journals/JIS/VOL13/Toth/toth10.pdf)

## Why the gcd term appears

Let $A$ be the odd least representatives in $\mathbb Z/k\mathbb Z$ and let $\sigma(x)$ equal $1$ on $A$ and $-1$ elsewhere, including at zero. Reflect both nonzero indices in the defining square. For odd representatives $h,j$, the four terms at $(\pm h,\pm j)$ add to $2\sigma(hj)$, even when $hj=0$ in the residue ring. Hence $S(k)=4\#\{(h,j)\in A^2:hj\in A\}-2m^2$. Reflecting just one coordinate would miss the nonunit products. [Odd-square identity](ThetaOddSquare.lean)

Write $A(t)=\sum_{a\in A}\exp(2\pi iat/k)$. Fourier inversion expands $k$ times this triple count as $\sum_t A(-t)\sum_{a\in A} A(at)$. At $t\ne0$, the two halves $A$ and $-A$ partition the nonzero residues, so $A(t)+A(-t)=-1$. The kernel of multiplication by $t$ has $d=\gcd(t,k)$ elements, and exactly $(d-1)/2$ of these lie in $A$. Each contributes $A(0)=m$. Pairing $t$ with $-t$ evaluates the entire singular contribution. [Frequency fibers](ThetaFrequencyFibers.lean) · [Exact decomposition](ThetaCompositeFourier.lean)

To bound the other terms, restrict the additive character at $t$ to the quotient of size $k/d$. Its values each occur $d$ times. The geometric-series bound and the reciprocal-sine estimate on that quotient give at most $kH_m$ for the regular slice, uniformly in $t$. Summing with the Fourier mass of the odd half, also at most $kH_m$, gives the squared harmonic error. [Common Fourier estimates](ThetaFourierBound.lean) · [Regular slice bound](ThetaFrequencyFibers.lean)

Finally the classical divisor identity gives
\[
 \frac{G(a^n)}{a^n}
  =\prod_{p\mid a,\ p\ {\rm prime}}
       \left(1+n\,v_p(a)\left(1-\frac1p\right)\right).
\]
The singular term thus grows with degree $r$ after division by $a^n$. The error after division by $a^n$ is $O_a(n^2)$. This proves the asserted negative leading term for $r\ge3$. The estimate alone leaves the sign on bases with one or two prime factors unresolved. [Divisor and prime-power computation](ThetaGcdMass.lean) · [Asymptotic transfer](ThetaCompositePowers.lean)

For $P_n$, multiplicativity gives $G(P_n)/P_n=\prod_{p\mid P_n}(2-1/p)\ge(3/2)^n$. Bertrand’s postulate bounds the $i$th prime (counting 2 at index zero) by $2^{i+1}$, hence $\log P_n\le n(n+1)\log 2$. Dividing the Fourier error by $G(P_n)$ bounds its magnitude by a constant times $n^4/(3/2)^n$. This proves the squarefree limit without the prime number theorem. [Squarefree proof](ThetaOddPrimorial.lean) · [Bertrand’s postulate in mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Bertrand.html#Nat.exists_prime_lt_and_le_two_mul)

## Verification and comparison

The growth-order estimate also follows by combining published results. For odd numerator $h<k$, Theorem 7.8 of Berndt et al. gives the row $1-\gcd(h,k)$. Pairing $h$ with $k-h$ in the gcd sum shows that all odd rows contribute $(2k-1-G(k))/2$. Each even row reduces, by the same theorem, to a primitive even row at $d=k/\gcd(h,k)$. For each divisor $d>1$ the primitive rows occur once; the Hardy–Dedekind identity and the first absolute moment bound (1) of Girstmair and Schoißengeier bound their total absolute value by $O(\varphi(d)\log^2(2d))$, using $\varphi(2d)=\varphi(d)$. Summing over divisors gives $O(k\log^2(2k))$ by $\sum_{d\mid k}\varphi(d)=k$. This inference from prior results also yields both negative families. The Lean proof gives the explicit harmonic error by a direct argument. [Paper, Theorem 7.8](https://arxiv.org/pdf/2501.03234v3#page=20) · [Hardy–Dedekind identities, Theorems 3 and 5](https://www.mdpi.com/2297-8747/21/3/31) · [Dedekind absolute moment, equation (1)](https://www.impan.pl/shop/en/publication/transaction/download/product/82121)

The proof imports the pinned canonical definition of $S$ and uses its exact floor, integer signs and both half-open intervals. It needs no prime number theorem or external analytic hypothesis. The existing DeepMind reduction explicitly uses primality in its treatment of the even columns. The OMA and Left to Solve records located by the paper ID concern prime reductions, finite certificates and harmonic bounds. The proof above uses both reflections over the full residue ring and accounts for all singular Fourier frequencies. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA finite certificate](https://github.com/lefttosolve2/open-math-agents/pull/21967) · [LTS solved feed](https://lefttosolve.com/api/solved)

Run the notebook’s aggregate replay from the pinned Formal Conjectures Lean 4.33.1 environment. The scoped check also rebuilds the existing direct consumer of the generalized Fourier estimate, `ThetaReciprocalCutoff`. The new theorem axiom reports contain only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the proof and verification. [Notebook replay](../../README.md#replay)
