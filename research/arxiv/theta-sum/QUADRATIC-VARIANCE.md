# Variance carried by prime quadratic characters

Put $R(p)=S(p)/p-\tfrac12\log p$ and let $\operatorname{Var}_X$ denote empirical variance with equal weight for the primes $p\le X$. For each odd prime $q$, let $C_q$ be the limiting prime mean of $R(p)(\frac pq)$. The uniformly convergent character series $Q(n)=\sum_q C_q(\frac nq)$ removes exactly
\[
 E=\sum_q C_q^2>\tfrac16
\]
from the limiting empirical variance. More precisely, there are finite $V,W$ with $\operatorname{Var}_X R\to V$, $\operatorname{Var}_X(R-Q)\to W$, and $V=E+W$ with $W\ge0$. The prime means of $Q^2$ and $(R-Q)Q$ tend to $E$ and $0$, respectively. Thus $V>1/6$. The preceding single-conductor bound was $V\ge C_3^2$, with $C_3^2\approx0.15879$. The value of $W$ and pointwise positivity at every odd prime remain open. The [composite character modulo fifteen](COMPOSITE-VARIANCE.md) subsequently gives $W>1/3600$. [Variance decomposition](ThetaQuadraticEnergy.lean) · [Certified lower bound](ThetaQuadraticCertificate.lean) · [Single-conductor result](EXACT-MOD-THREE-BIAS.md) · [Pinned definition of S](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean)

**Two finite cutoffs enclose $E$.** Choose an integer $Y>0$ with $\log Y\ge2$ and an integer $Z\ge2$. For $q\equiv3\bmod4$, put $H_q=\sum_{j=1}^{(q-1)/2}(\frac jq)$ and
\[
 A_q(Z)=\frac{\pi H_q^2\sqrt q}{(q-1)(q^2-1)}
  \prod_{\substack{2<\ell\le Z,\ \ell\ \mathrm{prime}\\(\frac{\ell}{q})=-1}}
  \left(1+\frac2{(\ell-1)^2}\right).
\]
Put $A_q(Z)=0$ for odd primes $q\equiv1\bmod4$ and $B(Y,Z)=\sum_{2<q\le Y,\ q\ \mathrm{prime}} A_q(Z)^2$. Then
\[
 B(Y,Z)<E\le B(Y,Z)\left(\frac{Z}{Z-1}\right)^4+
             \frac{20736(2+\log Y)^4}{Y^2}.
\]
In particular $B(Y,Z)/\pi^2$ is rational. Keeping the exact $C_q^2$ through $Y$ leaves a strictly positive error bounded by the final summand. The bounds quantify the prime-quadratic contribution $E$; the unexplained variance $W$ enters separately in $V$. [Conductor tail](ThetaQuadraticEnergyTail.lean) · [Local Euler-product intervals](QUADRATIC-EULER-PRODUCT.md)

## Derivation

Distinct prime Legendre characters have limiting inner product zero on the primes. Each has mean zero and squared mean norm one. For finitely many conductors one can therefore expand each covariance directly. To pass to the full series, the prime mean of $|R|$ stays bounded and the character series converges uniformly. More generally, if $f$ has bounded prime mean absolute value and all its prime Legendre correlations $b_q$ exist, the prime mean of $fQ$ is $\sum_q C_q b_q$ when the latter series is absolutely convergent. Apply this first to $f=R$ and then to $f=Q$, and recenter the empirical variance. [Uniform convergence and orthogonality](ThetaSpectrumDecay.lean) · [Pairing and variance identity](ThetaQuadraticEnergy.lean)

Dirichlet's theorem supplies a prime $q\equiv3\bmod4$ outside any finite conductor set. Its coefficient is nonzero, so every finite sum of squared coefficients is strictly below $E$. For the explicit $1/6$ bound, retain the conductors $3,7,11$, their half sums $1,1,3$, and the inert odd primes through $43$. The three finite Euler factors, in the same order, are
\[
 \frac{4529327622489}{3885629440000},\qquad
 \frac{20537400323}{11796480000},\qquad
 \frac{100081666172251}{91767649075200}.
\]
Substituting $3.14<\pi$ makes the remaining comparison rational. [Lean certificate](ThetaQuadraticCertificate.lean) · [Nonzero prime coefficients](PRIME-QUADRATIC-SPECTRUM.md)

For $q>Y$, set $t=(q/Y)^{1/4}$. From $\log t\le t-1$ and $2+\log Y\ge4$ one gets $2+\log q\le(2+\log Y)t$. Squaring the coefficient bound $|C_q|\le144(2+\log q)^2/q^{3/2}$ now gives $C_q^2\le20736(2+\log Y)^4/(Yq^2)$. Summing over all integers above $Y$ uses $\sum_{n>Y}1/n^2\le1/Y$. For the conductors through $Y$, square the relative Euler-product enclosure and sum. [Coefficient decay](QUADRATIC-EULER-PRODUCT.md) · [Tail proof](ThetaQuadraticEnergyTail.lean)

## Scope and replay

Berndt, Bhat, Meyer, Xie and Zaharescu conjecture positivity of the integer aggregate $S(p)$ for every odd prime. This result studies its centered prime distribution. Fixed-denominator moments of individual Hardy sums integrate over a different variable. The DeepMind, OMA and Left to Solve entries concern separate finite checks, reductions and harmonic bounds. [Original paper](https://arxiv.org/pdf/2501.03234v3) · [Guo and Zhang, Lemma 4](https://dml.cz/dmlcz/141636) · [Hardy and Kloosterman sums, Theorem 2](https://doi.org/10.1186/1029-242X-2014-52) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA harmonic bound](https://github.com/lefttosolve2/open-math-agents/pull/22818) · [Left to Solve](https://lefttosolve.com/api/solved)

The local proofs take the fixed-progression prime number theorem as input. The joint module below supplies it from the pinned PNT development. Save the block as `ThetaQuadraticEnergyPNT.lean`, compile it on the Euler-product replay search path and run `leanchecker -v ThetaQuadraticEnergyPNT`. Both unconditional declarations use only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the proof and verification. [Previous joint module](QUADRATIC-EULER-PRODUCT.md#joint-kernel-replay) · [Pinned external sources](QUADRATIC-EXCESS.md#joint-kernel-replay)

```lean
import ThetaQuadraticEnergyTail
import ThetaQuadraticCertificate
import ThetaConductorProductPNT

/-! Limiting empirical variance of the original centered theta sum and certified
finite approximations to its prime-quadratic component. -/
namespace Arxiv.«2501.03234».ThetaQuadraticEnergyPNT
open Finset Filter Topology ThetaNaturalPrimeMeans ThetaCharacterPrimeMeans ThetaSpectrumDecay
open ThetaConductorProduct ThetaConductorProductPNT ThetaQuadraticExcess ThetaQuadraticEnergy
open ThetaQuadraticEnergyTail ThetaPNTCorollaries

/-- The original centered sum has limiting empirical variance strictly above one sixth.
The variance removed by all prime-conductor quadratic modes is exactly the coefficient energy. -/
theorem original_variance :
    ∃ V W : ℝ, 1/6 < quadraticEnergy ∧ 0≤W ∧ V = quadraticEnergy+W ∧ 1/6<V ∧
      Tendsto (sampleVariance (fun p => (S p:ℝ)/p-Real.log p/2)) atTop (𝓝 V) ∧
      Tendsto (sampleVariance (fun p => (S p:ℝ)/p-Real.log p/2-quadraticPart p)) atTop (𝓝 W) ∧
      Tendsto (primeMean (fun p => (quadraticPart p)^2)) atTop (𝓝 quadraticEnergy) ∧
      Tendsto (primeMean (fun p => ((S p:ℝ)/p-Real.log p/2-quadraticPart p)*quadraticPart p))
        atTop (𝓝 0) := by
  obtain ⟨V,W,hW,he,hV,hrem,hQ,hcross⟩ := variance_decomposition progression_mangoldt
  have h := ThetaQuadraticCertificate.energy_gt_sixth progression_mangoldt
  exact ⟨V,W,h,hW,he,by linarith,hV,hrem,hQ,hcross⟩

/-- Lower approximation to one coefficient magnitude at Euler-prime cutoff n+2. -/
noncomputable def magnitudePrefix (q : OddPrime) (n : ℕ) : ℝ :=
  if q.val%4=3 then Real.pi*(excess q.val:ℝ)^2/Real.sqrt q.val*
    ((q.val:ℝ)/(((q.val:ℝ)-1)*((q.val:ℝ)^2-1)))*inertPrefix q.val n else 0

private theorem prefix_enclosure (q : OddPrime) (n : ℕ) :
    0 ≤ magnitudePrefix q n ∧ magnitudePrefix q n ≤ |coefficient q| ∧
      |coefficient q| ≤ magnitudePrefix q n * (((n:ℝ)+2)/(n+1))^2 := by
  by_cases hq : q.val%4=3
  · have hp : (2:ℝ)≤q.val := by exact_mod_cast q.property.1.two_le
    have hpref : 0 ≤ inertPrefix q.val n := by
      dsimp [inertPrefix]
      apply prod_nonneg
      intro l _
      simp only [inertFactor]
      split <;> positivity
    refine ⟨?_,?_⟩
    · simp only [magnitudePrefix,if_pos hq]
      apply mul_nonneg _ hpref
      apply mul_nonneg (by positivity) (div_nonneg (by positivity) (mul_nonneg (by linarith) (by nlinarith)))
    · simpa only [magnitudePrefix,if_pos hq] using coefficient_interval q hq n
  · have hodd := Nat.odd_iff.mp q.property.2
    have h₁ : q.val%4=1 := by omega
    have h := coefficient_limit progression_mangoldt q
    have h0 := ThetaPrimeSpectrum.even_character_mean q.val progression_mangoldt h₁
    simp only [ThetaLegendreFactors.symbol,legendreSym,Int.cast_natCast,ThetaCharacterPrimeMeans.residual] at h h0
    simp [magnitudePrefix,hq,tendsto_nhds_unique h h0]

/-- Both cutoffs are finite. B uses the Euler products through n+2 at conductors up to Y. -/
theorem effective_energy_interval {Y : ℕ} (hy : 0 < Y) (hlog : 2 ≤ Real.log Y) (n : ℕ) :
    let B := ∑ q∈conductorsThrough Y,(magnitudePrefix q n)^2
    B < quadraticEnergy ∧
      quadraticEnergy ≤ B*(((n:ℝ)+2)/(n+1))^4+20736*(2+Real.log Y)^4/(Y:ℝ)^2 := by
  have hτ := energy_truncation progression_mangoldt hy hlog
  let t := ((n:ℝ)+2)/(n+1)
  have hlo (q : OddPrime) : (magnitudePrefix q n)^2 ≤ (coefficient q)^2 := by
    rw [← sq_abs (coefficient q)]
    gcongr
    · exact (prefix_enclosure q n).1
    · exact (prefix_enclosure q n).2.1
  have hhi (q : OddPrime) : (coefficient q)^2 ≤ (magnitudePrefix q n)^2*t^4 := by
    rw [← sq_abs (coefficient q)]
    calc |coefficient q|^2 ≤ (magnitudePrefix q n*t^2)^2 := by
           gcongr
           exact (prefix_enclosure q n).2.2
         _ = _ := by ring
  have hL := sum_le_sum (s:=conductorsThrough Y) (fun q _ => hlo q)
  have hU := sum_le_sum (s:=conductorsThrough Y) (fun q _ => hhi q)
  rw [← sum_mul] at hU
  dsimp only
  change _ ∧ _ ≤ _ * t^4 + _
  constructor <;> linarith [hτ.1,hτ.2]

#print axioms original_variance
#print axioms effective_energy_interval
end Arxiv.«2501.03234».ThetaQuadraticEnergyPNT
```
