# How large can a progression mean be?

For a reduced class \(r\bmod m\), let \(\mu_{m,r}\) be the ordinary prime average of \(S(p)/p-\tfrac12\log p\) over that class, and let \(B\) be the corresponding all-prime mean. As the integer budget \(M\) tends to infinity,
\[
 \max_{1\le m\le M,\ (r,m)=1}|\mu_{m,r}-B|\asymp(\log\log M)^2.
\]
The upper constant is absolute. For any fixed reduced class \(r_0\bmod q\), every sufficiently large \(M\) admits a single \(m\le M\), divisible by \(q\), and two reduced classes modulo \(m\) above \(r_0\) whose means satisfy
\[
 \mu_{m,r_+}-B\ge\frac{(\log\log M)^2}{512\pi^2},\qquad
 \mu_{m,r_-}-B\le-\frac{(\log\log M)^2}{512\pi^2}.
\]
The threshold for \(M\) in the lower bound may depend on the prescribed class. Each mean takes the prime limit at its fixed modulus. The period budget in this result bounds the largest conditional bias; the [mean-square period budget](PERIOD-BUDGET.md) concerns the best global prediction error. [Extremal bounds](ThetaClassMeanBudget.lean) · [Original conditional mean](ThetaProgressionProjection.lean)

## Proof

Let \(D(m)=\sum_{g\mid m}1/g\) and \(L(m)=\sum_{g\mid m}(1+\log g)/g\). The absolute row bound on a fixed class factors through \(g=(d,m)\) and \(s=d/g\). The map \(d\mapsto (g,s)\) is injective. Its first coordinate contributes \(L(m)\); the second is bounded by a convergent reciprocal-power series. The uniform finite-model estimate passes to the limiting mean, and reflection of the centered predictor gives both signs. This proves \(|\mu_{m,r}-B|\le C_0 L(m)\) for every reduced class and \(m\ge1\). [Class estimate](ThetaUniformClassMeans.lean)

Set \(y=\lceil\log M\rceil\). For \(m\le M\), the primes \(p\mid m\) with \(p\le y\) give \(\sum (\log p)/p\le2\log y\) by the factorial estimate. Those above \(y\) contribute at most \((\log m)/y\le1\). The mean valuation of \(p\) under reciprocal divisor weights is at most \(1/(p-1)\). Thus \(L(m)\le7 D(m)\log y\) for \(\log y\ge1\). Divisors above \(y^{16}\) have total reciprocal mass at most \(D(m)/2\); the rest contribute at most the harmonic sum through \(y^{16}\). Consequently \(D(m)\le2+32\log y\) and \(L(m)\le238(\log y)^2\). This argument covers arbitrary prime factors in the modulus. [Divisor estimate](ThetaDivisorBudget.lean)

For the reverse bound take \(T=\lfloor\exp(\tfrac14\log\log M)\rfloor\). For large \(M\), the modulus \((T!)^T\) is at most \(M\), since its logarithm is at most \(T^3\), and \(\log T\ge\tfrac18\log\log M\). The two previously constructed class means above \(r_0\) then supply the stated constants. [Two signed class means](ThetaCompatibleMeans.lean) · [Excursions of the prime values](ALL-CLASS-EXCURSIONS.md)

## Source and replay

The bounds concern class averages of the centered original sum. Pointwise positivity and eventual lower growth along all primes remain open. The primary paper asks the pointwise questions. The DeepMind row reduction and OMA’s fixed-depth continued-fraction integral and grid results address different steps toward pointwise growth. [Paper](https://arxiv.org/pdf/2501.03234v3) · [Pinned integer definition and hypotheses](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean) · [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA harmonic bound](https://github.com/lefttosolve2/open-math-agents/pull/22818) · [Continued-fraction reduction](https://github.com/lefttosolve2/open-math-agents/pull/21388) · [Integral means](https://github.com/lefttosolve2/open-math-agents/pull/27960) · [Grid convergence](https://github.com/lefttosolve2/open-math-agents/pull/28015) · [Left to Solve](https://lefttosolve.com/api/solved)

The following bridge discharges the fixed-progression prime number theorem and states both bounds directly in the original sum. [Pinned PNT and replay](NATURAL-PRIME-MEAN.md#joint-lean-replay)

```lean
import ThetaClassMeanBudget
import ThetaPNTCorollaries

/-! Exact order of the extremal signed conditional means of the original prime sum. -/
namespace Arxiv.«2501.03234».ThetaClassMeanBudgetPNT
open Filter Real ThetaNaturalPrimeMeans ThetaProgressionProjection ThetaDiagonalConstant ThetaDyadicLaw
open scoped Topology

theorem all_means :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ M : ℕ in atTop, ∀ m r : ℕ, 0 < m → m≤ M → r< m → r.Coprime m →
      ∃ L : ℝ, Tendsto (progressionMean m r (fun p => (S p:ℝ)/p-log p/2)) atTop (𝓝 L) ∧
        |L-diagonalConstant|≤ C*(log (log M))^2 := by
  have hAP : ProgressionMangoldt := ThetaPNTCorollaries.progression_mangoldt
  obtain ⟨C,hC,H⟩ := ThetaClassMeanBudget.upper hAP
  refine ⟨C,hC,H.mono fun M h m r hm hM hr hc => ?_⟩
  let : NeZero m := ⟨hm.ne'⟩
  exact ⟨_,original_mean m r hc hr hAP,by simpa only [add_sub_cancel_left] using h m r hM hr hc⟩

theorem opposite_means {q r : ℕ} (hq : 0 < q) (hr : r < q) (hc : r.Coprime q) :
    ∀ᶠ M : ℕ in atTop,
      ∃ m : ℕ, 0 < m ∧ m≤ M ∧ q∣m ∧ ∃ n< m, ∃ s< m,
        n.Coprime m ∧ s.Coprime m ∧ n%q=r ∧ s%q=r ∧ ∃ U L : ℝ,
        Tendsto (progressionMean m n (fun p => (S p:ℝ)/p-log p/2)) atTop (𝓝 U) ∧
        Tendsto (progressionMean m s (fun p => (S p:ℝ)/p-log p/2)) atTop (𝓝 L) ∧
        diagonalConstant+(log (log M))^2/(512*Real.pi^2)≤ U ∧
          L≤ diagonalConstant-(log (log M))^2/(512*Real.pi^2) := by
  have hAP : ProgressionMangoldt := ThetaPNTCorollaries.progression_mangoldt
  filter_upwards [ThetaClassMeanBudget.lower hAP hq hr hc] with M h
  obtain ⟨m,hm,hM,hqm,n,hn,s,hs,hnc,hsc,hnq,hsq,hpos,hneg⟩ := h
  let : NeZero m := hm
  refine ⟨m,NeZero.pos m,hM,hqm,n,hn,s,hs,hnc,hsc,hnq,hsq,_,_,original_mean m n hnc hn hAP,
    original_mean m s hsc hs hAP,?_,?_⟩
  · linarith only [hpos]
  · linarith only [hneg]

#print axioms all_means
#print axioms opposite_means
end Arxiv.«2501.03234».ThetaClassMeanBudgetPNT
```
