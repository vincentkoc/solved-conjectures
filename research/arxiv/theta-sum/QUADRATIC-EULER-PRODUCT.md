# Euler products for quadratic prime correlations

Let $R(p)=S(p)/p-\tfrac12\log p$ for the original integer theta sum. Write $C_q$ for the ordinary prime mean of $\chi_q(p)R(p)$, where $\chi_q=(\frac{\cdot}{q})$ and $q$ is an odd prime. For every $q\equiv3\bmod4$, put $H_q=\sum_{j=1}^{(q-1)/2}\chi_q(j)$. Then
$$
 C_q=-\chi_q(2)\,\frac{\pi H_q^2\sqrt q}{(q-1)(q^2-1)}
       \prod_{\substack{\ell\ {\rm odd\ prime}\\\chi_q(\ell)=-1}}
                 \left(1+\frac{2}{(\ell-1)^2}\right).
$$
For $q\equiv1\bmod4$ the correlation vanishes. At $q=3$ the factor outside the product is $3\pi/(16\sqrt3)$, and the inert odd primes are precisely $5\bmod6$. This recovers the earlier conductor-three formula. The general formula evaluates the correlations for both signed conductor classes. [Conductor-three evaluation](EXACT-MOD-THREE-BIAS.md) · [Zero class and existence](PRIME-QUADRATIC-SPECTRUM.md) · [Quadratic-excess sign](QUADRATIC-EXCESS.md)

**Each finite cutoff certifies the error uniformly in the conductor.** Let $U_q(Y)$ be the product over eligible primes through the integer $Y\ge2$, and $U_q$ its infinite value. Then
$$
             U_q(Y)\le U_q\le U_q(Y)\left(\frac{Y}{Y-1}\right)^2.
$$
In particular $1\le U_q\le4$. Multiplying by $\pi H_q^2\sqrt q/((q-1)(q^2-1))$ gives an enclosure for $|C_q|$ from finite arithmetic. The upper endpoint has relative excess at most $2/(Y-1)+1/(Y-1)^2$. For conductor three, $(Y/(Y-1))^2$ also sharpens the earlier tail factor $\exp(2/(Y-1))$. [Local factors and certified interval](ThetaConductorProduct.lean)

**The coefficients are absolutely summable over all odd prime conductors.** The proof gives
$$
              |C_q|\le\frac{144(2+\log q)^2}{q\sqrt q}
                  \qquad (q\equiv3\bmod4).
$$
Consequently $Q(n)=\sum_q C_q\chi_q(n)$ converges uniformly for all natural $n$. Removing this series from the original residual cancels every odd prime-conductor quadratic bias.
$$
 \lim_{X\to\infty}\frac1{\pi(X)}\sum_{p\le X,\ p\ {\rm prime}}
        \chi_q(p)\bigl(R(p)-Q(p)\bigr)=0.
$$
Here the character is zero at its conductor. Other characters and the untwisted mean can still contribute to the residual. [Decay, uniform convergence and orthogonality](ThetaSpectrumDecay.lean)

## Proof

The earlier row transfer expresses $C_q$ as $P_qL_q$ times a sum of nonnegative amplitudes over $d$, with $P_q=-2\chi_q(2)H_q$ and $L_q=\sum_{n\ge1}\chi_q(n)/n$ in natural order. Define the multiplicative weight
$$
 F_q(d)=\frac{\mathbf1_{d\ {\rm odd}}}{d\varphi(d)}
        \prod_{\ell\mid d,\ \ell\ {\rm prime}}
             (1-\chi_q(\ell))(1-\chi_q(\ell)/\ell)
$$
for $d\ge1$, with $F_q(0)=0$. The row amplitude is $(1-\chi_q(2)/2)F_q(d)\mathbf1_{q\mid d}$. For positive $d$ prime to $q$, $F_q(qd)=F_q(q)F_q(d)$. The summability of row amplitudes thus bounds both the coprime and divisible parts of $F_q$. Subtracting the Euler product restricted to integers prime to $q$ from the full Euler product extracts the $q$-power contribution. [Multiplicativity and summability](ThetaConductorProduct.lean)

At $\ell=q$ the positive-exponent local sum is $q/((q-1)(q^2-1))$. At each odd $\ell\ne q$, the local sum including exponent zero is $1+2/(\ell-1)^2$ for $\chi_q(\ell)=-1$ and $1$ for $\chi_q(\ell)=1$. The prime 2 contributes $1$. Multiplying the resulting product by $P_qL_q(1-\chi_q(2)/2)$ and applying the half-period identity eliminates $L_q$. The finite-product upper certificate follows because $U_q(Y)(Y/(Y-1))^2$ decreases with $Y$ while $U_q(Y)$ increases. The character harmonic tail estimate at cutoff $q$ gives $L_q\le 2+\log q$. Together with $U_q\le4$ this yields the displayed coefficient bound. [Character tail estimate](ThetaLegendreFactors.lean) · [Dirichlet half-period identity](QUADRATIC-EXCESS.md)

For distinct prime conductors the Chinese remainder theorem gives zero mean for the product of the two characters on reduced residues. A character has square one on the units of its own conductor. The prime number theorem in fixed progressions transfers these identities to the ordinary prime mean. For a finite character sum containing the tested conductor, its prime correlation is exactly the corresponding coefficient in the limit. Uniform convergence of the series permits passage to the full quadratic component, with an error bounded by the uniform approximation error. [Prime orthogonality](ThetaPrimeSpectrum.lean) · [Projection](ThetaSpectrumDecay.lean)

## Scope and comparison

Berndt, Bhat, Meyer, Xie and Zaharescu study an aggregate of Hardy sums appearing in the theta transformation. The pinned DeepMind conjecture asks for $S(p)>0$ at every odd prime. These Euler products and the orthogonal remainder concern the centered sum averaged over primes. Pointwise positivity remains open. The [variance decomposition](QUADRATIC-VARIANCE.md) identifies and bounds the part of the limiting variance captured by these coefficients. Guo and Zhang expand individual Hardy sums at a fixed denominator by characters of that denominator. Theorem 2 of the 2014 Hardy and Kloosterman paper has a class-number square and a modulo-eight split for a weighted numerator average at a fixed prime. In the formula here the denominator prime varies and the Legendre test conductor stays fixed. The DeepMind issue, OMA proofs and LTS result concern remainder reductions, finite checks and a harmonic bound. [Original paper](https://arxiv.org/pdf/2501.03234v3) · [Pinned upstream sum](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean) · [Guo and Zhang, Lemma 4](https://dml.cz/dmlcz/141636) · [Hardy and Kloosterman sums, Theorem 2](https://doi.org/10.1186/1029-242X-2014-52) · [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA harmonic bound](https://github.com/lefttosolve2/open-math-agents/pull/22818) · [LTS solved feed](https://lefttosolve.com/api/solved)

## Joint kernel replay

The notebook modules use the pinned Lean 4.33.1 environment. The following module discharges the progression theorem and the positive phase of the prime Gauss sum using the same verified source extraction as the signed excess result. Save the Lean block as `ThetaConductorProductPNT.lean` beside the compiled `ThetaExcessSignsPNT` module, compile it on that search path and run `leanchecker -v ThetaConductorProductPNT`. The six final declarations use only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the derivation and formalization. [Source pins and replay commands](QUADRATIC-EXCESS.md#joint-kernel-replay)

```lean
import ThetaSpectrumDecay
import ThetaExcessSignsPNT

/-! The signed Euler product, the certified finite cutoff, and the summable spectrum. -/
namespace Arxiv.«2501.03234».ThetaConductorProductPNT
open Finset Filter Topology ThetaPrimeSpectrum ThetaConductorProduct ThetaQuadraticExcess
open ThetaSpectrumDecay ThetaNaturalPrimeMeans ThetaPNTCorollaries ThetaLegendreFactors

private theorem signed_value (q : OddPrime) (hq : q.val%4=3) :
    coefficient q = -(legendreSym q.val 2:ℝ)*
      (Real.pi*(excess q.val:ℝ)^2/Real.sqrt q.val*
        ((q.val:ℝ)/(((q.val:ℝ)-1)*((q.val:ℝ)^2-1)))*inertProduct q.val) := by
  have H := coefficient_limit progression_mangoldt q
  obtain ⟨C,hC,hmag,_⟩ := correlation_size q.val progression_mangoldt hq
  obtain ⟨D,hD,h3,h7,_⟩ := ThetaExcessSignsPNT.signed_correlation q.val hq
  have he (p : ℕ) : legendreSym q.val (p:ℤ)=symbol q.val p := by
    simp only [legendreSym,symbol,Int.cast_natCast]
  rw [← tendsto_nhds_unique H hD] at h3 h7
  simp only [he,ThetaCharacterPrimeMeans.residual] at H hC
  rw [← tendsto_nhds_unique H hC] at hmag
  rw [← hmag]
  have h2 := legendreSym.at_two (p:=q.val) (by omega : q.val≠2)
  rw [ZMod.χ₈_nat_mod_eight] at h2
  rcases (show q.val%8=3 ∨ q.val%8=7 by omega) with h|h
  · rw [h] at h2; rw [h2,show ZMod.χ₈ ((3:ℕ):ZMod 8)= -1 by decide,abs_of_pos (h3 h)]; norm_num
  · rw [h] at h2; rw [h2,show ZMod.χ₈ ((7:ℕ):ZMod 8)=1 by decide,abs_of_neg (h7 h)]; norm_num

/-- The ordinary prime correlation of the original residual, evaluated exactly. -/
theorem signed_euler_product (q : OddPrime) (hq : q.val%4=3) :
    Tendsto (primeMean (fun p => (legendreSym q.val (p:ℤ):ℝ)*((S p:ℝ)/p-Real.log p/2)))
      atTop (𝓝 (-(legendreSym q.val 2:ℝ)*
        (Real.pi*(excess q.val:ℝ)^2/Real.sqrt q.val*
          ((q.val:ℝ)/(((q.val:ℝ)-1)*((q.val:ℝ)^2-1)))*inertProduct q.val))) :=
  signed_value q hq ▸ coefficient_limit progression_mangoldt q

/-- The finite product through n+2 encloses the magnitude with a relative gap
independent of the prime conductor. -/
theorem coefficient_interval (q : OddPrime) (hq : q.val%4=3) (n : ℕ) :
    let A := Real.pi*(excess q.val:ℝ)^2/Real.sqrt q.val*
      ((q.val:ℝ)/(((q.val:ℝ)-1)*((q.val:ℝ)^2-1)))*inertPrefix q.val n
    A ≤ |coefficient q| ∧ |coefficient q| ≤ A*(((n:ℝ)+2)/(n+1))^2 := by
  obtain ⟨C,hC,hmag,hprod⟩ := correlation_size q.val progression_mangoldt hq
  have H := coefficient_limit progression_mangoldt q
  have he (p : ℕ) : legendreSym q.val (p:ℤ)=symbol q.val p := by
    simp only [legendreSym,symbol,Int.cast_natCast]
  simp only [he,ThetaCharacterPrimeMeans.residual] at H hC
  rw [← tendsto_nhds_unique H hC] at hmag
  let M := Real.pi*(excess q.val:ℝ)^2/Real.sqrt q.val*
    ((q.val:ℝ)/(((q.val:ℝ)-1)*((q.val:ℝ)^2-1)))
  have hp : (2:ℝ)≤q.val := by exact_mod_cast q.property.1.two_le
  have hM : 0≤M := by
    apply mul_nonneg (by positivity) (div_nonneg (by positivity) (mul_nonneg (by linarith) (by nlinarith)))
  change M*inertPrefix q.val n ≤ _ ∧ _ ≤ M*inertPrefix q.val n*_
  change |coefficient q|=M*inertProduct q.val at hmag
  rw [hmag]
  exact ⟨mul_le_mul_of_nonneg_left (hprod n).1 hM,by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hprod n).2 hM⟩

theorem absolute_prime_spectrum : Summable (fun q : OddPrime => |coefficient q|) :=
  summable_coefficients progression_mangoldt

theorem uniform_prime_spectrum :
    TendstoUniformly (fun (s : Finset OddPrime) (n : ℕ) =>
      ∑ q∈s, coefficient q*(legendreSym q.val (n:ℤ):ℝ))
      (fun n => ∑' q : OddPrime,coefficient q*(legendreSym q.val (n:ℤ):ℝ)) atTop :=
  uniform_quadratic_series progression_mangoldt

/-- Uniform decay of the original prime correlation at every conductor with odd character. -/
theorem coefficient_decay (q : OddPrime) (hq : q.val%4=3) :
    |coefficient q| ≤ 144*(2+Real.log q.val)^2/((q.val:ℝ)*Real.sqrt q.val) := by
  apply correlation_decay q.val progression_mangoldt hq
  have H := coefficient_limit progression_mangoldt q
  simpa only [legendreSym,symbol,Int.cast_natCast,ThetaCharacterPrimeMeans.residual] using H

/-- The ordinary prime average of every odd-prime Legendre twist of the remainder is zero. -/
theorem residual_after_quadratic_part (q : OddPrime) :
    Tendsto (primeMean (fun p => (legendreSym q.val (p:ℤ):ℝ)*
      ((S p:ℝ)/p-Real.log p/2-quadraticPart p))) atTop (𝓝 0) :=
  orthogonal_remainder progression_mangoldt q

#print axioms coefficient_decay
#print axioms residual_after_quadratic_part
#print axioms signed_euler_product
#print axioms coefficient_interval
#print axioms absolute_prime_spectrum
#print axioms uniform_prime_spectrum
end Arxiv.«2501.03234».ThetaConductorProductPNT
```
