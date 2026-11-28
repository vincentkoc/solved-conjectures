# Concentration and all prime moments of the theta sum

Write \(R(p)=S(p)/p-\tfrac12\log p\). There are absolute constants \(C,a>0\) such that for **every** integer \(X\ge2\) and every real \(t\ge0\),
\[
 \#\{p\le X:p\ {\rm prime},\ |R(p)|\ge t\}
 \le C\,\pi(X)\exp(-a\sqrt t).
\]
The same constants bound the limiting probability \(\mu\{|x|>t\}\). The prime count in the prefactor is essential for a bound uniform in the empirical probability measure. The earlier estimate has \(X\) in that position. [Sieved concentration](ThetaSievedConcentration.lean) · [Earlier count](PRIME-CONCENTRATION.md)

For every continuous real test \(\phi\) satisfying \(|\phi(x)|\le K(1+|x|^k)\) for some \(K\ge0\) and integer \(k\ge0\),
\[
 \frac{1}{\pi(X)}\sum_{p\le X}\phi(R(p))\longrightarrow \int\phi\,d\mu.
\]
Here and below prime sums run over primes. Restricting to *any fixed reduced class* modulo \(2^\ell\) and dividing by its own prime count gives the very same limit. In particular every absolute and signed moment converges. Writing \(B\) for the ordinary prime mean of \(R\), every centered odd moment converges to zero, including along primes congruent to one modulo eight. There are also \(b,D>0\) such that the empirical averages of \(\exp(b\sqrt{|R(p)|})\) are at most \(D\) for all \(X\ge2\), and its integral under \(\mu\) is at most \(D\). [Moment and dyadic transfer](ThetaResidualMoments.lean) · [Definition of the center](ThetaDiagonalConstant.lean)

## Where the prime count enters

Use the cone on a band \(N^{56}\le p\le N^{64}\). For \(1\le T\le N\), rows of denominator at most \(T\) contribute \(O((1+\log T)^2)\) uniformly. The rows from \(T\) to \(N\) have prime mean-square sum \(O(N^{64}T^{-1/8}/\log N)\) by the prime sieve. The higher rows have integer mean-square sum \(O(N^{64}N^{-1/64})\). Since \(\log N\ll N^{1/128}\), the latter is also \(O(N^{64}/(T^{1/128}\log N))\). An error above a sufficiently large constant times \((1+\log T)^2\) forces the sum of the latter two magnitudes to exceed one. For \(T>N\), the earlier bound \(O(N^{64}T^{-1/64})\) absorbs \(\log N\) directly. [Sieved middle rows](ThetaSievedWindows.lean) · [High-row variance](ThetaDenominatorTails.lean)

The same earlier estimate handles primes below \(N^{56}\). Choosing \(N=1+\lfloor X^{1/64}\rfloor\) and applying Chebyshev's lower bound for \(\pi(X)\) gives \(O(\pi(X) T^{-1/128})\) uniformly in \(T\). Choosing \(T\) exponential in \(\sqrt t\) gives the displayed tail estimate. The constants are existential. This count gives no pointwise sign conclusion for every prime. [Cutoff and endpoint transfer](ThetaSievedConcentration.lean)

Portmanteau transfers the bound for open tails to the weak limit. Layer cake applied to \(U=(a/2)\sqrt{|x|}\) gives \(\int e^U\,d\mu\le1+C\), since \(\Pr(U>s)\le Ce^{-2s}\) for \(s\ge0\). The same calculation holds for the empirical measures. A polynomial-growth test has uniformly bounded second moment. Clipping its values at \(\pm M\) costs at most that moment divided by \(M\), so weak convergence applies after clipping and the error tends to zero. For a fixed dyadic class, the reciprocal of its limiting prime density bounds the change of normalization up to a constant. Reflection of the limiting law about \(B\) then gives the odd-moment identity. [Weak convergence and reflection](ThetaPrimeResidualLaw.lean) · [Prime distribution by dyadic class](ThetaDyadicLaw.lean)

## Sources and joint replay

Berndt, Bhat, Meyer, Xie and Zaharescu ask for the sign and growth of this same signed double sum over prime denominators. Liu and Zhang give power means of individual Hardy sums over numerators for a fixed denominator. The empirical law here takes one value of the signed aggregate for each varying prime. The linked DeepMind and OMA reductions cover other aspects of the conjecture. [Original paper, §3](https://arxiv.org/pdf/2501.03234v3#page=4) · [Pinned canonical sum and predicates](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean) · [Liu and Zhang](https://www.i-repository.net/contents/osakacu/sugaku/111F0000002-04104-1.pdf) · [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA finite bound](https://github.com/lefttosolve2/open-math-agents/pull/18042) · [LTS solved list](https://lefttosolve.com/solved)

The finite count uses the notebook sieve and the pinned sum directly. The limiting statements use the prime number theorem in each fixed progression. The following combined module discharges that input, and states the conclusions on the original \(S\). Codex assisted with the derivation and verification. [Joint replay instructions](NATURAL-PRIME-MEAN.md#joint-lean-replay)

```lean
import ThetaResidualMoments
import ThetaPNTCorollaries

/-! Exponential tails and all polynomial moments of the original prime theta sum. -/
namespace Arxiv.«2501.03234».ThetaResidualMomentsPNT
open Filter Topology MeasureTheory ThetaPrimeDensity ThetaNaturalPrimeMeans ThetaPrimeLaw ThetaDyadicLaw
open ThetaResidualMoments ThetaDiagonalConstant

/-- A single prime limiting law for all continuous polynomial-growth tests,
including each fixed reduced dyadic progression. -/
theorem original_law_and_moments :
    ∃ μ : ProbabilityMeasure ℝ,
      Tendsto (empirical (fun p => (S p:ℝ)/p-Real.log p/2)) atTop (𝓝 μ) ∧
      (∃ C a : ℝ, 0<C ∧ 0<a ∧
        (∀ t : ℝ, 0≤t → (μ:Measure ℝ).real {x : ℝ | t< |x|}≤C*Real.exp (-a*Real.sqrt t)) ∧
        ∀ X : ℕ, 2≤X → ∀ t : ℝ, 0≤t → ((primeSet (fun p => t≤|(S p:ℝ)/p-Real.log p/2|) X).card:ℝ)
            ≤C*Nat.primeCounting X*Real.exp (-a*Real.sqrt t)) ∧
      ∀ (φ : ℝ → ℝ), Continuous φ → ∀ (K : ℝ) (k : ℕ), (∀ x, |φ x|≤K*(1+|x|^k)) →
        Integrable φ (μ:Measure ℝ) ∧
        Tendsto (primeMean (fun p => φ ((S p:ℝ)/p-Real.log p/2))) atTop (𝓝 (∫ x, φ x ∂(μ:Measure ℝ))) ∧
        ∀ {l r : ℕ}, r.Coprime (2^l) → r<2^l →
          Tendsto (progressionMean (2^l) r (fun p => φ ((S p:ℝ)/p-Real.log p/2))) atTop
            (𝓝 (∫ x, φ x ∂(μ:Measure ℝ))) := by
  have hAP : ProgressionMangoldt := ThetaPNTCorollaries.progression_mangoldt
  obtain ⟨F,hF⟩ := exists_haar_representative hAP residual_approximable
  refine ⟨haarLaw F,empirical_tendsto hAP hF,prime_and_limit_tails hAP hF,?_⟩
  intro φ hc K k hg
  obtain ⟨hi,hlim⟩ := prime_polynomial_growth hAP hF hc hg
  refine ⟨hi,hlim,?_⟩
  intro l r hr hlt
  exact dyadic_polynomial_growth hAP hF hr hlt hc hg

theorem uniform_prime_exponential_moment :
    ∃ b D : ℝ, 0<b ∧ 0<D ∧ ∀ X : ℕ, 2≤X →
      primeMean (fun p => Real.exp (b*Real.sqrt |(S p:ℝ)/p-Real.log p/2|)) X≤D := by
  have hAP : ProgressionMangoldt := ThetaPNTCorollaries.progression_mangoldt
  obtain ⟨F,hF⟩ := exists_haar_representative hAP residual_approximable
  obtain ⟨b,D,hb,hD,_,H⟩ := exponential_square_root hAP hF
  exact ⟨b,D,hb,hD,H⟩

theorem centered_odd (k : ℕ) :
    Tendsto (primeMean (fun p => ((S p:ℝ)/p-Real.log p/2-diagonalConstant)^(2*k+1))) atTop (𝓝 0) ∧
    ∀ {l r : ℕ}, r.Coprime (2^l) → r<2^l →
      Tendsto (progressionMean (2^l) r (fun p => ((S p:ℝ)/p-Real.log p/2-diagonalConstant)^(2*k+1))) atTop (𝓝 0) :=
  odd_centered_moments ThetaPNTCorollaries.progression_mangoldt k

end Arxiv.«2501.03234».ThetaResidualMomentsPNT
#print axioms Arxiv.«2501.03234».ThetaResidualMomentsPNT.original_law_and_moments
#print axioms Arxiv.«2501.03234».ThetaResidualMomentsPNT.uniform_prime_exponential_moment
#print axioms Arxiv.«2501.03234».ThetaResidualMomentsPNT.centered_odd
```
