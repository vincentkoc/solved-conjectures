# Full variance and progression means of the prime theta sum

Write \(R(p)=S(p)/p-\tfrac12\log p\), and let \(B\) be its ordinary prime mean. For each primitive Dirichlet character \(\chi\) of conductor \(q\), define \(C_\chi\) by the prime mean of \((R(p)-B)\chi(p)\). The variance of \(R\) has the convergent expansion
\[
 \lim_{X\to\infty}\frac1{\pi(X)}\sum_{p\le X}
 \left(R(p)-\frac1{\pi(X)}\sum_{r\le X,\ r\ {\rm prime}}R(r)\right)^2
 = V = \sum_{q\ge1}\ \sum_{\chi\ {\rm primitive}\bmod q}|C_\chi|^2.
\]
Only odd characters of odd conductor contribute. For every positive integer \(Y\),
\[
 0\le V-\sum_{q\le Y}\ \sum_{\chi\ {\rm primitive}\bmod q}|C_\chi|^2
 \le \frac{449280}{Y}.
\]
This bound controls truncation in conductor. Each retained coefficient has an \(L\)-value and an absolutely convergent Euler product. Numerical evaluation of those factors requires its own error control. [Parseval identity](ThetaSpectralVariance.lean) · [Conductor cutoff](ThetaInverseConductorTail.lean) · [Coefficient formula](PRIMITIVE-SPECTRUM.md)

## The best predictor at a fixed modulus

Fix \(m\ge1\) and a reduced class \(r\bmod m\). The mean of \(R(p)\) over primes in that class, divided by the number of those primes, converges to
\[
 B+\sum_{q\mid m}\ \sum_{\chi\ {\rm primitive}\bmod q}
             C_\chi\,\overline{\chi(r)} .
\]
The sum is real by conjugate symmetry. Using the class mean as the predictor for each class gives a limiting mean square error of exactly \(\sum_{q\nmid m}\sum_\chi |C_\chi|^2\). Any real \(m\)-periodic predictor has limiting error at least this large. If every odd \(q\le Y\) divides \(m\), the cutoff bound above applies to its optimal error. At \(m=8\) the predictor equals \(B\) on every reduced class, since the centered principal and all even-conductor modes vanish. These are aggregate conclusions for the original double sum. The pointwise positivity question for each prime remains open. [Class mean](ThetaProgressionProjection.lean) · [Finite least-squares identity](ThetaFiniteProjection.lean) · [Missing conductors](ThetaFullVarianceTail.lean)

## Proof

Finite character orthogonality gives the least-squares identity at each modulus. The centered residual has periodic approximations in ordinary prime mean square by the rational-row tail estimate. Fourier inversion on the units therefore exhausts the limiting variance along factorial moduli. Descending every lifted character to its primitive conductor gives one term per primitive character. [Approximation and inversion](ThetaVarianceExhaustion.lean) · [Descent](ThetaLevelCoefficients.lean) · [Counting primitive characters once](ThetaSpectralVariance.lean)

For a contributing character of conductor \(q\), let \(W_\chi\) be its weight Euler product. Applying the finite Fourier transform twice gives the primitive Gauss magnitude \(\sqrt q\). The coefficient then satisfies
\[
 |C_\chi|
 =\frac{(5-4\Re\chi(2))\,|L(1,\chi)|^2|W_\chi|}
        {\pi\sqrt q\,\varphi(q)} .
\]
A telescoping majorant for the local factors gives \(1\le |W_\chi|\le4\). Over the nonprincipal characters modulo any \(q\), the sum of \(|L(1,\chi)|^4\) is at most \(520\varphi(q)\). To see this, truncate the harmonic character series just before \(q\), with error at most one. Finite character orthogonality and Cauchy–Schwarz bound the normalized fourth moment of the truncation by \((\sum_{n\ge1} n^{-4/3})^3\le64\). The inequality \((x+1)^4\le8(x^4+1)\) gives the stated constant. Hence the total squared coefficient mass at \(q>1\) is at most \(74880/(q\varphi(q))\). [Magnitude identity](ThetaConductorDecay.lean) · [Finite Fourier inequality](ThetaFourthMoment.lean) · [Fourth moment at one](ThetaLValueMoment.lean) · [Single-conductor mass](ThetaConductorMoment.lean)

Expand \(q/\varphi(q)=\prod_{p\mid q}(1+1/(p-1))\) over subsets of prime divisors. The reciprocal-square sum of multiples of \(d\) starting at \(Y\) is at most \(2/(dY)\). Summing the subset weights gives a product bounded by \(\exp(\sum_{n\ge2}1/(n(n-1)))=e<3\). Thus \(\sum_{q\ge Y}1/(q\varphi(q))\le6/Y\). The proof bounds every finite subset directly. It also implies the weaker bound \(576(2+\log Y)^5/Y\) for \(\log Y\ge8\). [Totient tail](ThetaTotientTail.lean) · [Full cutoff and its consequences](ThetaInverseConductorTail.lean)

## Source comparison and replay

Berndt, Bhat, Meyer, Xie and Zaharescu conjecture pointwise positivity and growth for the same \(S(p)\). The pinned formalization defines the integer double sum and states the lower-growth side of Conjecture 3.3. The upstream issue and OMA work concern finite checks and remainder estimates. Guo and Zhang derive fixed-denominator Hardy-sum identities. The variance here averages the normalized double sum over varying prime denominators, against characters of fixed conductor. [Original conjectures](https://arxiv.org/pdf/2501.03234v3#page=4) · [Pinned source](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA remainder reduction](https://github.com/lefttosolve2/open-math-agents/pull/22818) · [OMA finite check](https://github.com/lefttosolve2/open-math-agents/pull/18042) · [Left to Solve](https://lefttosolve.com/api/solved) · [Guo and Zhang](https://dml.cz/dmlcz/141636)

The following module discharges the fixed-progression prime number theorem with the pinned external proof. Each of its six declarations uses only the standard axioms _propext_, _Classical.choice_ and _Quot.sound_. [PNT source and replay](NATURAL-PRIME-MEAN.md#joint-lean-replay)

```lean
import ThetaInverseConductorTail
import ThetaProgressionProjection
import ThetaPNTCorollaries

/-! Complete prime spectral variance and conditional means of the original theta sum. -/
namespace Arxiv.«2501.03234».ThetaSpectralVariancePNT
open ThetaFullVarianceTail ThetaInverseConductorTail Filter Topology ThetaNaturalPrimeMeans ThetaSpectralVariance ThetaCharacterPrimeMeans
open ThetaDiagonalConstant ThetaProgressionProjection ThetaFiniteProjection ThetaDyadicLaw

theorem full_variance :
    Summable Mode.mass ∧ Tendsto (sampleVariance (fun p => (S p : ℝ) / p - Real.log p / 2)) atTop
      (𝓝 (∑' u : Mode, u.mass)) :=
  original_variance ThetaPNTCorollaries.progression_mangoldt

theorem reduced_class_mean (m r : ℕ) [NeZero m] (hr : r.Coprime m) (hlt : r < m) :
    Tendsto (progressionMean m r (fun p => (S p : ℝ) / p - Real.log p / 2)) atTop
      (𝓝 (diagonalConstant + predictor m r)) :=
  original_mean m r hr hlt ThetaPNTCorollaries.progression_mangoldt

theorem remaining_variance (m : ℕ) [NeZero m] :
    Tendsto (primeMean (fun p => ((S p : ℝ) / p - Real.log p / 2 - diagonalConstant - predictor m p)^2))
      atTop (𝓝 ((∑' u : Mode, u.mass) - energy m)) := by
  have hAP : ProgressionMangoldt := ThetaPNTCorollaries.progression_mangoldt
  obtain ⟨_,V,_,_,_,_,hV,_⟩ := S_prime_class_statistics hAP
  have h := optimal_error m hV hAP
  rw [(parseval hV hAP).tsum_eq]
  exact h

/-- Truncation by primitive conductor in the full variance of the original sum. -/
theorem finite_variance (Y : ℕ) (hy : 0 < Y) :
    ∑ u ∈ through Y, u.mass ≤ ∑' u : Mode, u.mass ∧
    ∑' u : Mode, u.mass ≤ ∑ u ∈ through Y, u.mass + 449280/Y := by
  have hAP : ProgressionMangoldt := ThetaPNTCorollaries.progression_mangoldt
  obtain ⟨_,V,_,_,_,_,hV,_⟩ := S_prime_class_statistics hAP
  rw [(parseval hV hAP).tsum_eq]
  exact truncation hV hAP Y hy

/-- The omitted primitive-conductor mass is the optimal prediction error. -/
theorem missing_conductors (m : ℕ) [NeZero m] :
    HasSum (fun u : Mode => if u.modulus ∣ m then 0 else u.mass) ((∑' u : Mode, u.mass)-energy m) := by
  have hAP : ProgressionMangoldt := ThetaPNTCorollaries.progression_mangoldt
  obtain ⟨_,V,_,_,_,_,hV,_⟩ := S_prime_class_statistics hAP
  rw [(parseval hV hAP).tsum_eq]
  exact missing_mass hV hAP m

/-- Empirical variance with the finite-conductor interval on its actual limit. -/
theorem original_variance_cutoff (Y : ℕ) (hY : 0 < Y) :
    ∃ V : ℝ, Tendsto (sampleVariance (fun p => (S p : ℝ)/p-Real.log p/2)) atTop (𝓝 V) ∧
      0 ≤ V-∑ u∈through Y,u.mass ∧ V-∑ u∈through Y,u.mass ≤ 449280/Y := by
  exact ⟨_, full_variance.2, by linarith [(finite_variance Y hY).1],
    by linarith [(finite_variance Y hY).2]⟩

#print axioms original_variance_cutoff
#print axioms finite_variance
#print axioms missing_conductors
#print axioms full_variance
#print axioms reduced_class_mean
#print axioms remaining_variance
end Arxiv.«2501.03234».ThetaSpectralVariancePNT
```
