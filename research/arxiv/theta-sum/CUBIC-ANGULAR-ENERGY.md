# Directional signs and energy of the prime theta coefficients

For a nonprincipal character \(\chi\bmod p\), put \(A_\chi=\sum_{a=1,3,\ldots,p-2}\chi(a)\) and \(C_\chi=A_\chi^2\overline{A_\chi}\). The canonical signed integer sum satisfies \((p-1)S(p)=4\sum_{\chi\ne1}C_\chi\). The imaginary parts cancel in this last sum by character conjugation. Their squares retain information about the phases of the individual coefficients. [Exact expansion](ThetaPointwiseCubic.lean) · [Pinned sum and positivity conjecture](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean#L36-L64)

### Directional signs and deletion

There is an absolute \(\delta>0\) such that for every fixed \(\varepsilon>0\), every sufficiently large odd prime \(p\), and every unit \(z\in\mathbb C\), at least \(\delta p\) nonprincipal characters of order \(>p^{1-\varepsilon}\) satisfy
\[
     \operatorname{Re}(zC_\chi)\ \ge\ p\sqrt p/8192 .
\]
Taking \(-z\) gives the opposite sign with the same threshold and count. In particular, after deleting any set of fewer than \(\delta p\) characters, the real convex hull of the remaining high-order points \(C_\chi/(p\sqrt p)\) contains the closed disk of radius \(1/8192\) centered at zero. Both the deleted set and the direction can depend on \(p\). [Directional count](ThetaDirectionalProportions.lean) · [Disk inclusion](ThetaCubicHull.lean)

The proof starts with the half sums. Inversion pairs make the mixed real-imaginary second moment vanish. The count of odd representatives with odd inverse bounds both diagonal second moments below by \(p^2/32\) for large primes. Since \(C_\chi=|A_\chi|^2A_\chi\), a cutoff at \(\sqrt p/8\) gives absolute projected cubic mass at least \(p^{5/2}/512\). The exact expansion of \(S(p)\) bounds the signed projected mass uniformly, leaving positive mass at least \(p^{5/2}/2048\). The fourth moment bounds the contribution from very large \(|A_\chi|\), and the divisor bound shows that characters below the order cutoff have density zero. A separating linear functional would expose a direction missing from the surviving points, which proves the disk inclusion. [Half-sum covariance](ThetaDirectionalHalfMoment.lean) · [Projected cubic mass](ThetaDirectionalMass.lean) · [Fourth moment](ThetaHalfFourthMoment.lean)

## Projected energy

For each odd prime write \(E=\sum_{\chi\ne1}|C_\chi|^2\) and \(E_R=\sum_{\chi\ne1}(\operatorname{Re}C_\chi)^2\). Then
\[
  E\ge\frac{(p-1)^4}{64},\qquad
  \left|\frac{E_R}{E}-\frac12\right|\le
     1536\,\frac{H_{(p-1)/2}^6}{p^{1/4}}.
\]
In particular the fraction tends to \(1/2\) along all primes. The same finite error holds simultaneously for every unit complex \(z\) when \(E_R\) is replaced by \(\sum (\operatorname{Re}(zC_\chi))^2\). The axis may therefore depend on the prime. For every fixed \(\varepsilon>0\), convergence to \(1/2\) is still uniform in the axis when both sums are restricted to characters with \(\operatorname{ord}(\chi)>p^{1-\varepsilon}\). These are second moments of the coefficients of the original sum. The sign of their first moment remains open for the full prime family. [Explicit bounds](ThetaCubicEnergy.lean) · [All nonprincipal characters](ThetaCubicEnergyLimit.lean) · [Large orders](ThetaHighAngularEnergy.lean) · [Uniformity in the projection axis](ThetaRotatedEnergy.lean)

## The second angular harmonic

Write \(\phi=p-1\), \(H=H_{(p-1)/2}\). For every nonnegative integer \(r\), the finite proof gives
\[
 \left|\sum_{\chi\ne1} A_\chi^{r+2}\overline{A_\chi}^{\,r}\right|
 \le p^r(2\phi p^{3/4}+1)H^{2r+2}.
\]
For \(r=2\) the summands are precisely \(C_\chi^2\). The real part measures the difference between real and imaginary energy. [Formal moment inequality](ThetaAngularMoments.lean)

Writing \(\tau_\chi=\sum_x\chi(x)e_p(x)\), orthogonality gives
\[
   \sum_{\chi\bmod p}\tau_\chi^2\chi(u)=\phi K(1,u^{-1}).
\]
The principal term is 1. The notebook's elementary three-quarter-power Kloosterman bound therefore controls the second angular harmonic uniformly in the twisting unit \(u\). Additive completion expresses \(A_\chi/\tau_\chi\) as a linear combination of character values with coefficient norm sum at most \(H\). Multiplying a test by this transform or its conjugate costs at most \(H\) at each step. This proves the displayed moment bound by \(2r+2\) multiplications. [Twisted Gauss identity](ThetaGaussAngularKernel.lean) · [Multiplicative tests](ThetaAngularTests.lean) · [Elementary Kloosterman bound](ThetaReciprocalCutoff.lean)

For the denominator, orthogonality gives \(\sum_{\chi\ne1}|A_\chi|^2=\phi^2/4\). For \(m=\phi/4\) the identity \(y^3-3m^2y+2m^3=(y-m)^2(y+2m)\) gives the lower bound for \(E\) by summation with \(y=|A_\chi|^2\). Counting small-order characters by divisors of \(p-1\) and using the uniform half-interval bound gives total energy \(o_\varepsilon(p^4)\) for the discarded orders. [Radial lower bound](ThetaCubicEnergy.lean) · [Discarded orders](ThetaSparseCubicEnergy.lean)

Hussain's Propositions 3.4–3.7 already give quantitative mixed moments of normalized character paths at fixed parameters, and Lemma 3.8 bounds powers of Gauss sums with an arbitrary multiplicative twist via Deligne. Those estimates give the uniform-phase limit and a stronger analytic input for the second harmonic. Here the odd-representative sum equals the ordinary half-interval sum multiplied by \(-\chi(2)\) for nonprincipal characters, so the second harmonic carries an additional twist \(\chi(4)\). The notebook gives an independently checked elementary bound with explicit constants and transfers it to the cubic energy after deleting low-order characters. Earlier fourth-power character-sum literature includes Xu and Zhang. The live DeepMind reduction expresses the problem through a residual sum. The LTS positivity certificate checks every odd prime below 100,000. Both concern the signed sum itself. Codex assisted with derivation and formalization. [Hussain, Propositions 3.4–3.7 and Lemma 3.8](https://arxiv.org/pdf/2010.06967#page=12) · [Xu–Zhang](https://www.impan.pl/shop/publication/transaction/download/product/82312) · [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA](https://github.com/lefttosolve2/open-math-agents/pull/21388) · [LTS finite positivity certificate](https://github.com/lefttosolve2/open-math-agents/pull/21967)
