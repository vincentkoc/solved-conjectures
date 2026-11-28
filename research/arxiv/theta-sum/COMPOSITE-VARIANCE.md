# A composite character survives the prime quadratic projection

Let $R(p)=S(p)/p-\tfrac12\log p$ for the original integer theta sum. Let $Q(p)=\sum_{q\ \mathrm{odd\ prime}} C_q(\frac pq)$ be the uniformly convergent sum of all its prime Legendre modes. The Jacobi character $\psi(p)=(\frac p{15})$ has an ordinary prime correlation
\[
 C=\lim_{X\to\infty}\frac1{\pi(X)}\sum_{p\le X}\psi(p)(R(p)-Q(p))<-\frac1{60}.
\]
Its correlation with $R$ alone has the same value. Consequently the limiting empirical variances $V$ of $R$ and $W$ of $R-Q$ satisfy
\[
 V=\sum_q C_q^2+W,\qquad W\ge C^2>\frac1{3600},\qquad V>\frac{601}{3600}.
\]
The preceding decomposition gave $W\ge0$. This witness proves that the infinite series of all prime Legendre modes leaves a strictly positive part of the variance. The value of $W$ and the sign of $S(p)$ at every odd prime remain open. [Composite correlation and variance](ThetaCompositeVariance.lean) · [Preceding variance decomposition](QUADRATIC-VARIANCE.md) · [Pinned upstream definition and positivity conjecture](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean)

There is also a uniform threshold for periodic corrections. For every positive fixed $m$ with $15\nmid m$ and every $g:\mathbb Z/m\mathbb Z\to\mathbb R$, all sufficiently large $X$ satisfy
\[
 \frac1{\pi(X)}\sum_{p\le X}|R(p)-Q(p)-g(p\bmod m)|>\frac1{60}.
\]
The endpoint cutoff can depend on $m$ and $g$. This includes arbitrarily large periods divisible by one of 3 and 5. The earlier periodic-model inequality concerned approximating $R$ by a finite-period function alone. [Error transfer](ThetaPrimeSpectrum.lean) · [Earlier fixed-period bounds](QUADRATIC-EXCESS.md)

## Proof

The Chinese remainder theorem factors $\psi$ as the product of the mod-3 and mod-5 Legendre characters. If $15\nmid d$, at least one factor is centered and independent of both the other factor and the periodic test modulo $d$. Thus every row at such a denominator has zero twisted mean, including the cases where $d$ contains powers of 3 or 5 individually. Taking $d$ to be any prime conductor and passing to the uniformly convergent series shows that the prime mean of $\psi Q$ is zero. [Finite cancellation and prime transfer](ThetaFifteenOrthogonality.lean) · [Uniform series](QUADRATIC-EULER-PRODUCT.md)

For odd $d$ divisible by 15, inclusion and exclusion in the row sum retain only primes dividing $d$ and coprime to 15. The denominator factors $1-\psi(\ell)$ and $1-\psi(\ell)/\ell$ are nonnegative. All these rows have the same signed factor $-4L$, where
\[
 \sum_{j=0}^{14}(-1)^{j+1}\psi(j)=-4,\qquad
 L=\lim_{K\to\infty}\sum_{j=1}^K\frac{\psi(j)}j>1.
\]
For the last inequality the exact sum through $29$ is $767097285/492929008$ and the harmonic tail at cutoff $30$ has absolute value at most $15/30$. The weight of the $d=15$ row alone is $1/240$. Keeping this row gives $C\le -L/60<-1/60$. The general row identity applies to every Jacobi modulus greater than one dividing the odd row denominator. The spectral nonvanishing proof here uses conductor 15. [Jacobi row factorization](ThetaJacobiRows.lean) · [Harmonic certificate](ThetaJacobiFifteen.lean) · [Row-to-prime transfer](ThetaPrimeSpectrum.lean)

The finite inequality $2C\psi z-C^2\le z^2$ for $|\psi|\le1$ bounds the limiting variance from below after centering $z$ by the mean of $R-Q$. The periodic-correction bound follows by testing its absolute error against the same character. Both transfers use ordinary prime counts. [Variance and absolute-error theorems](ThetaCompositeVariance.lean)

## Scope and replay

The source conjectures in Berndt, Bhat, Meyer, Xie and Zaharescu concern pointwise positivity, growth and congruences. Guo and Zhang expand individual Hardy sums for fixed denominators. The weighted Hardy and Kloosterman identity of Theorem 2 in the 2014 paper also fixes the prime denominator. Here the denominator prime varies, the test conductor is fixed, and the quantity is the centered original aggregate after subtracting its prime-conductor component. The DeepMind issue and the OMA and Left to Solve results concern other reductions and bounds. [Original paper](https://arxiv.org/pdf/2501.03234v3) · [Guo and Zhang](https://dml.cz/dmlcz/141636) · [Hardy and Kloosterman sums, Theorem 2](https://doi.org/10.1186/1029-242X-2014-52) · [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA proof](https://github.com/lefttosolve2/open-math-agents/pull/22818) · [LTS feed](https://lefttosolve.com/api/solved)

The local prime-average theorems take the fixed-progression prime number theorem as input. Save the block as `ThetaCompositeVariancePNT.lean`, compile it on the preceding joint replay path and run `leanchecker -v ThetaCompositeVariancePNT`. The two unconditional declarations use only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the proof and verification. [Previous joint module](QUADRATIC-VARIANCE.md#scope-and-replay) · [Source pins](QUADRATIC-EXCESS.md#joint-kernel-replay)

```lean
import ThetaCompositeVariance
import ThetaQuadraticEnergyPNT

/-! Unconditional composite witness on the original centered theta sum. -/
namespace Arxiv.«2501.03234».ThetaCompositeVariancePNT
open Filter Topology ThetaNaturalPrimeMeans ThetaCharacterPrimeMeans ThetaPNTCorollaries
open ThetaSpectrumDecay ThetaQuadraticEnergy ThetaCompositeVariance

/-- The conductor-fifteen Jacobi correlation survives every prime-conductor subtraction.
The full empirical variance exceeds 601/3600. -/
theorem original_variance :
    ∃ C V W : ℝ, C < -(1/60) ∧ C^2≤W ∧ 1/3600<W ∧ 601/3600<V ∧ V=quadraticEnergy+W ∧
      Tendsto (primeMean (fun p => (jacobiSym (p:ℤ) 15:ℝ)*((S p:ℝ)/p-Real.log p/2-quadraticPart p))) atTop (𝓝 C) ∧
      Tendsto (sampleVariance (fun p => (S p:ℝ)/p-Real.log p/2)) atTop (𝓝 V) ∧
      Tendsto (sampleVariance (fun p => (S p:ℝ)/p-Real.log p/2-quadraticPart p)) atTop (𝓝 W) := by
  obtain ⟨C,V,W,hn,hl,hw,he,hc,hV,hW⟩ := residual_variance progression_mangoldt
  have hq := ThetaQuadraticCertificate.energy_gt_sixth progression_mangoldt
  exact ⟨C,V,W,hn,hl,hw,by linarith,he,hc,hV,hW⟩

/-- A fixed residue correction that omits either 3 or 5 leaves an error above 1/60,
even after including all odd prime-conductor Legendre modes. -/
theorem period_gap (m : ℕ) [NeZero m] (hm : ¬15∣m) (g : ZMod m → ℝ) :
    ∀ᶠ X : ℕ in atTop, 1/60 < primeMean (fun p => |(S p:ℝ)/p-Real.log p/2-quadraticPart p-g (p:ZMod m)|) X := by
  apply corrected_period_gap progression_mangoldt hm
  intro n
  simp

#print axioms original_variance
#print axioms period_gap
end Arxiv.«2501.03234».ThetaCompositeVariancePNT
```
