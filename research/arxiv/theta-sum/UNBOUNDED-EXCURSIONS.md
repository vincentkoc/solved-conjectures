# Unbounded prime excursions of the theta sum

Write $R(p)=S(p)/p-\tfrac12\log p$ for the residual of the original integer double sum. For every real $b>0$, both $R(p)>b$ and $R(p)<-b$ occur with positive lower prime density inside **each fixed reduced residue class modulo a power of two**. In particular this holds for $p\equiv1\pmod8$. Each density uses the number of *all* primes up to $X$ in the denominator. The lower bounds can depend on the threshold and the class. The limiting probability law gives positive mass to both open tails at every height. [Original Lean sum](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean) · [Dyadic limiting law](DYADIC-PRIME-LAW.md)

There is also a class-mean statement. For every real $b$ there is a fixed $m>1$ for which the ordinary mean of $R(p)$ over $p\equiv1\pmod m$ converges to a number greater than $b$. These means use the prime count in the specific class. An excursion of fixed size in $R(p)$ changes $S(p)$ by order $p$. Pointwise positivity of $S(p)$ and the paper's eventual lower bound for all primes remain open. [Paper, section 3](https://arxiv.org/pdf/2501.03234v3#page=4) · [Identity progression means](ThetaIdentityPrimeMeans.lean)

## Why the progression mean grows

For odd $d>1$ and any positive numerator cutoff $K$, the reciprocal row at the identity is at least $1/2$. The first term is one. All terms of its sign sequence through $d$ are nonnegative, reflection gives the opposite signs in the second half-period, and each complete period sums to zero. Abel summation therefore gives a lower bound uniform in $K$. If $d\mid m$, conditioning the model on the class $1\bmod m$ returns precisely this row. [Identity row](ThetaIdentityRow.lean) · [Conditional residue calculation](ThetaIdentityFiber.lean)

For the other denominators put $g=(m,d)$ and $s=d/g$. In a complete period divisible by $d$ and $m$, the unit-group mean of the selected row, multiplied by $\varphi(m)$, has absolute value at most $3H_d\tau(s)/\varphi(s)$. Splitting into fibers modulo $g$ leaves one residue to estimate. After division by $d$, the bound is at most $1080(1+\log g)g^{-1}s^{-19/16}$. This gives uniform control of the absolute contribution from arbitrary finite sets of omitted denominators. [Row envelope](ThetaSmoothRows.lean)

Take $m=(T!)^A$ and let $D(m)=\sum_{g\mid m}1/g$ and $L(m)=\sum_{g\mid m}(1+\log g)/g$. Here $D(m)\ge H_T$ for $A\ge1$. The odd divisors greater than one have reciprocal mass at least $D(m)/2-1$. For each prime $p$, weighting the layers $p^i\mid g$ by $1/g$ bounds the total valuation by $D(m)/(p-1)$. Since each prime divisor of $m$ is at most $T$, this gives $L(m)\le D(m)[1+2\log T(1+\log T)]$. [Reciprocal divisor moments](ThetaDivisorLogMean.lean)

If $s\ge T$, summation of the row envelope costs $O(T^{-1/16}L(m))$. If $1<s<T$, any prime $p\mid s$ forces $p^A\mid g$. Division by $p^A$ bounds the logarithmically weighted mass of such divisors by $(L(m)+A\log T\,D(m))/p^A$. Summing the possible small primes costs at most $T/2^A$ times the numerator. First take $T$ large and then $A$ large. After including the bounded common-factor weights the total error is at most $D(m)/8$, uniformly in both model cutoffs. The captured rows contribute at least $D(m)/4-1/2$. [Omitted rows](ThetaFactorialRows.lean) · [Choice of modulus](ThetaIdentityModulus.lean) · [Finite-model inequality](ThetaIdentityModels.lean)

The ordinary prime mean approximation for the reciprocal model applies to the bounded selector of a fixed progression. Dividing by that progression's positive prime density gives the class-mean conclusion. A class mean beyond a threshold yields positive lower prime density beyond that threshold. Closed half-lines pass to the common limiting law. Reflection about the diagonal constant gives the lower tail, and weak convergence in each reduced dyadic class transfers both open tails back to ordinary prime counts. [Prime class transfer](ThetaIdentityPrimeMeans.lean) · [Law and original-sum density](ThetaUnboundedExcursions.lean)

## Source comparison and replay

The original paper studies positivity, growth and congruences of $S(p)$. The linked reductions concern sign estimates or finite verification. The fixed-denominator character formulas for individual Hardy sums use a different averaging variable. The earlier notebook gave positive lower densities beyond specific thresholds. Here the threshold is arbitrary on each side of the same centered original sum. [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA reduction](https://github.com/lefttosolve2/open-math-agents/pull/22818) · [Finite verification](https://github.com/lefttosolve2/open-math-agents/pull/18042) · [Left to Solve](https://lefttosolve.com/api/solved) · [Guo and Zhang](https://dml.cz/dmlcz/141636)

The notebook declarations take the prime number theorem in progressions as an explicit input. The following module uses the pinned external proof through the [combined replay bridge](NATURAL-PRIME-MEAN.md).

```lean
import ThetaPNTCorollaries
import ThetaUnboundedExcursions

/-! Unconditional prime excursions of the original theta residual. -/

namespace Arxiv.«2501.03234».ThetaUnboundedExcursionsPNT
open Filter MeasureTheory ThetaProfiniteUnits ThetaDyadicLaw ThetaNaturalPrimeMeans ThetaPrimeLaw
open scoped Topology

theorem identity_means (b : ℝ) : ∃ m : ℕ, 1 < m ∧ ∃ L : ℝ, b < L ∧
    Tendsto (progressionMean m 1 (fun p => (S p : ℝ)/p - Real.log p/2)) atTop (𝓝 L) :=
  ThetaIdentityPrimeMeans.arbitrarily_large ThetaPNTCorollaries.progression_mangoldt b

theorem law : ∃ F : G →₁[haar] ℝ,
    Represents (fun p => (S p : ℝ)/p - Real.log p/2) F ∧
    ∀ b : ℝ, 0 < (haarLaw F : Measure ℝ) (Set.Ioi b) ∧ 0 < (haarLaw F : Measure ℝ) (Set.Iio b) := by
  obtain ⟨F,hF⟩ := exists_haar_representative ThetaPNTCorollaries.progression_mangoldt residual_approximable
  exact ⟨F,hF,ThetaUnboundedExcursions.unbounded_law ThetaPNTCorollaries.progression_mangoldt hF⟩

theorem dyadic_tails (b : ℝ) {k r : ℕ} (hr : r.Coprime (2^k)) (hlt : r < 2^k) :
    PositiveLowerPrimeDensity (fun p => p%(2^k)=r ∧ b < (S p:ℝ)/p-Real.log p/2) ∧
    PositiveLowerPrimeDensity (fun p => p%(2^k)=r ∧ (S p:ℝ)/p-Real.log p/2 < -b) :=
  ThetaUnboundedExcursions.original ThetaPNTCorollaries.progression_mangoldt b hr hlt

theorem one_mod_eight (b : ℝ) :
    PositiveLowerPrimeDensity (fun p => p%8=1 ∧ b < (S p:ℝ)/p-Real.log p/2) ∧
    PositiveLowerPrimeDensity (fun p => p%8=1 ∧ (S p:ℝ)/p-Real.log p/2 < -b) :=
  dyadic_tails b (k:=3) (r:=1) (by decide) (by decide)

#print axioms identity_means
#print axioms law
#print axioms dyadic_tails
#print axioms one_mod_eight
end Arxiv.«2501.03234».ThetaUnboundedExcursionsPNT
```
