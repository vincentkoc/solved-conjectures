# The optimal period budget for predicting the prime theta sum

For a real function \(g\) of integer period \(m\), write
\[
 L(g)=\lim_{X\to\infty}\frac1{\pi(X)}
 \sum_{\substack{p\le X\\p\ \mathrm{prime}}}
 \left(\frac{S(p)}p-\tfrac12\log p-g(p)\right)^2 .
\]
Every such limit exists. If the period is limited to \(1\le m\le M\), the smallest achievable limiting mean square error has order
\[
                \frac{1}{\log M\,\log\log M}.
\]
More precisely, for every sufficiently large integer \(M\), every admissible model has \(L(g)\ge 2^{-34}/(\log M\,\log\log M)\), and one real model has \(L(g)\le C/(\log M\,\log\log M)\) for an absolute \(C>0\). The period and the model are chosen before the prime endpoint tends to infinity. The minimum at a fixed modulus is attained by its class-mean predictor. These quantifiers concern the best fixed congruence predictors of the signed aggregate. Pointwise positivity remains open. [Original-sum theorem](ThetaBudgetOriginal.lean) · [Exact projection error](ThetaProgressionProjection.lean) · [Qualitative criterion for sequences of periods](MODEL-PERIODS.md)

## Upper bound

Take \(m=\operatorname{lcm}(1,\ldots,Y)\). Chebyshev's upper bound for \(\psi(Y)=\log m\) gives \(\log m\le6Y\). By Parseval the optimal prediction error is the total mass of conductors \(q\nmid m\), and the mass at each \(q>1\) is at most a constant times \(1/(q\varphi(q))\). [Parseval and conductor moment](SPECTRAL-VARIANCE.md)

For each prime \(p\), let \(h_p=p^{1+\lfloor\log_p Y\rfloor}\). Each missing \(q\) is a multiple of at least one such \(h_p\). Totient supermultiplicativity and the reciprocal-totient estimate bound the sum of \(1/(q\varphi(q))\) over its multiples by \(6/(h_p\varphi(h_p))\le12/h_p^2\). In a band \(H\le h_p\le2H\) there are at most \(\pi(2H)\) choices, since their prime bases are distinct and \(p\le h_p\). The sum over that band is \(O(1/(H\log H))\). Summing the decreasing geometric tail from \(H\ge Y\) gives \(O(1/(Y\log Y))\). With \(Y=\lfloor\log M/6\rfloor\), this period is affordable. [Missing prime powers](ThetaMissingPrimePowers.lean) · [Prime count by band](ThetaPrimePowerPacking.lean) · [Model error](ThetaPeriodBudget.lean)

## Lower bound

Every period with \(\log m\le6Y\) omits at least \(Y/\log Y\) primes in \((Y,128Y]\) for all sufficiently large \(Y\). Indeed the product of the primes in this band dividing \(m\) is at most \(m\). The logarithmic cost per such prime exceeds \(\log Y\), whereas Chebyshev's lower bound for \(\pi(128Y)\) and upper bound for \(\pi(Y)\) supply more primes than the period can contain. [Omitted prime band](ThetaMissingPrimeBand.lean)

At every prime \(p\ge1025\), the conductor defect is \(1/(p-1)\le1/1024\). The primitive odd characters at this level contribute at least \(1/(2^{20}p^2)\) to the variance. Each omitted level in the band therefore costs at least \(1/(2^{34}Y^2)\). Summing the disjoint levels proves the lower bound. Taking \(Y=1+\lfloor\log M/6\rfloor\) covers every allowed period. [Prime-level mass](ThetaConductorLayerLower.lean) · [Disjoint-level lower bound](ThetaSharpPeriodBudget.lean)

## Sources and replay

The published conjectures concern sign and growth for the canonical integer sum. The DeepMind and OMA work below gives other reductions and finite bounds. Guo and Zhang study character expressions for Hardy sums with fixed denominator. The budget theorem optimizes mean square error for the full signed integer sum as its prime denominator varies. [Berndt et al., §3](https://arxiv.org/pdf/2501.03234v3#page=4) · [Canonical source](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA](https://github.com/lefttosolve2/open-math-agents/pull/18042) · [LTS](https://lefttosolve.com/solved) · [Guo and Zhang](https://dml.cz/dmlcz/141636)

The notebook uses the prime number theorem in fixed progressions in identifying the signed theta projection. The following bridge supplies that theorem and exports both sides with the original \(S\). Codex assisted with the derivation and verification. [PNT source and replay](NATURAL-PRIME-MEAN.md#joint-lean-replay)

```lean
import ThetaBudgetOriginal
import ThetaPNTCorollaries

/-! The best periodic mean-square prediction rate for the original signed sum. -/
namespace Arxiv.«2501.03234».ThetaPeriodBudgetPNT
open Filter Topology ThetaNaturalPrimeMeans ThetaPeriodMeans

theorem original_budget :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ M : ℕ in atTop,
      (∀ m : ℕ, 0 < m → m≤M → ∀ g : ℕ → ℝ, OnMod m g → ∃ L : ℝ,
        Tendsto (primeMean (fun p => (((S p:ℝ)/p-Real.log p/2)-g p)^2)) atTop (𝓝 L) ∧
        1/((1048576*128^2)*Real.log M*Real.log (Real.log M))≤L) ∧
      ∃ m : ℕ, 0 < m ∧ m≤M ∧ ∃ g : ℕ → ℝ, OnMod m g ∧ ∃ L : ℝ,
        Tendsto (primeMean (fun p => (((S p:ℝ)/p-Real.log p/2)-g p)^2)) atTop (𝓝 L) ∧
        L≤C/(Real.log M*Real.log (Real.log M)) :=
  ThetaPeriodBudget.optimal_model_rate ThetaPNTCorollaries.progression_mangoldt

#print axioms original_budget
end Arxiv.«2501.03234».ThetaPeriodBudgetPNT
```
