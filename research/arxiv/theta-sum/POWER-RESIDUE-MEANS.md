# Mean bias from bounded-order characters

Let \(R(p)=S(p)/p-\tfrac12\log p\) and let \(B\) be its all-prime mean. Fix \(k\ge1\). There is a constant \(C_k\) such that for every \(m\ge1\) and every nonempty union \(A\) of cosets of \(((\mathbb Z/m\mathbb Z)^\times)^k\), the prime mean of \(R(p)\) restricted to \(p\bmod m\in A\) exists and differs from \(B\) by at most \(C_k\). The same constant covers all moduli and all sizes of \(A\), including a single coset. For odd \(k\) the mean equals \(B\). [Original prime theorem](ThetaPowerResiduePrimeMeans.lean) · [Invariance and odd-power symmetry](ThetaPowerResidueMeans.lean)

Any condition determined by the values of characters satisfying \(\chi^k=1\) is invariant under multiplication by \(k\)th powers. For \(k=2\) the theorem covers any joint pattern of quadratic residue tests with at least one admissible unit class. In contrast, unrestricted reduced classes can have centered means of order \((\log\log M)^2\) with moduli at most \(M\). Hence no fixed bound on character order can produce that unbounded mean bias, even if the number of tests grows. The modulus is fixed before taking the prime limit in both theorems. [Unrestricted class means](EXTREME-CLASS-MEANS.md)

## Weighted absolute convergence

For every \(\delta<1/2\), the primitive spectrum satisfies
\[
 \sum_{\substack{\chi\ \mathrm{primitive}\\\chi^k=1}}
     \operatorname{cond}(\chi)^\delta |C_\chi| < \infty .
\]
Here \(C_\chi\) is the limiting prime correlation of the centered original residual. The sum counts each character at its unique primitive conductor. For \(0<\delta<1/2\) it gives a uniform \(O_{k,\delta}(Y^{-\delta})\) bound for the absolute mass omitted above conductor \(Y\), also for character subsets at any imprimitive level. The proof gives no endpoint claim at \(\delta=1/2\). [Primitive series and finite tail](ThetaBoundedOrderSpectrum.lean) · [Coefficient normalization](PRIMITIVE-SPECTRUM.md)

At an odd modulus \(q\) there are at most \(k^{\omega(q)}\) characters killed by \(k\). Duality identifies the character group with the unit group. The odd prime-power factors are cyclic and the Chinese remainder theorem multiplies the counts. The totient factor satisfies \(q/\varphi(q)\le2^{\omega(q)}\), and \((2k)^{\omega(q)}=O_{k,\epsilon}(q^\epsilon)\) for every \(\epsilon>0\). Combining these estimates with the primitive coefficient bound \(12(2+\log q)^2/(\sqrt q\,\varphi(q))\) gives absolute convergence after conductor weighting. Even-conductor coefficients vanish. [Character count](ThetaCharacterTorsion.lean) · [Subpower bound](ThetaTorsionMajorant.lean) · [Summable conductor bound](ThetaBoundedOrderLayers.lean)

In a union of power cosets, translation by a \(k\)th power leaves the selected units invariant. This annihilates the average of each character with \(\chi^k\ne1\). The absolute sum of the remaining coefficients therefore bounds the conditional mean, without a factor inverse to the size of the selection. When \(k\) is odd, the selection is invariant under negation, and the opposite centered predictors cancel in pairs. Equidistribution in each reduced class then transfers the finite average to the original selected primes. [Cancellation](ThetaPowerResidueMeans.lean) · [Prime transfer](ThetaPowerResiduePrimeMeans.lean)

## Source and replay

The paper and the pinned DeepMind source concern pointwise growth and positivity for \(S(p)\). The present result concerns conditional means under residue tests, extending the earlier estimate for the quadratic coefficients at odd prime conductors to all primitive conductors and any fixed exponent. Pointwise positivity remains open. [Paper](https://arxiv.org/pdf/2501.03234v3) · [Pinned sum and conjectures](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean) · [Prime-conductor quadratic coefficients](QUADRATIC-EULER-PRODUCT.md) · [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA harmonic estimate](https://github.com/lefttosolve2/open-math-agents/pull/22818) · [Left to Solve](https://lefttosolve.com/api/solved)

The bridge uses the pinned prime number theorem in progressions. [PNT source and replay](NATURAL-PRIME-MEAN.md#joint-lean-replay)

```lean
import ThetaPowerResiduePrimeMeans
import ThetaPNTCorollaries

/-! Uniform conditional prime means for all fixed-exponent power-residue data. -/
namespace Arxiv.«2501.03234».ThetaPowerResiduePrimeMeansPNT
open Filter Real ThetaDyadicLaw ThetaDiagonalConstant ThetaPowerResidueMeans ThetaPowerResiduePrimeMeans
open ThetaSpectralVariance ThetaBoundedOrderSpectrum
open scoped Topology

theorem bounded_tests {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0≤ C ∧ ∀ m : ℕ, [NeZero m] → ∀ A : Finset (ZMod m)ˣ, A.Nonempty → Stable k A →
      ∃ L : ℝ, |L-diagonalConstant|≤ C ∧
        Tendsto (predicateMean (allows A) (fun p => (S p:ℝ)/p-log p/2)) atTop (𝓝 L) :=
  original ThetaPNTCorollaries.progression_mangoldt hk

theorem odd_tests {k m : ℕ} [NeZero m] (hk : _root_.Odd k)
    (A : Finset (ZMod m)ˣ) (ha : A.Nonempty) (hA : Stable k A) :
    Tendsto (predicateMean (allows A) (fun p => (S p:ℝ)/p-log p/2)) atTop (𝓝 diagonalConstant) :=
  original_odd ThetaPNTCorollaries.progression_mangoldt hk A ha hA

theorem conductor_weight {k : ℕ} (hk : 0 < k) {δ : ℝ} (hd : δ < 1/2) :
    Summable (weight k δ) := summable_weight ThetaPNTCorollaries.progression_mangoldt hk hd

#print axioms bounded_tests
#print axioms odd_tests
#print axioms conductor_weight
end Arxiv.«2501.03234».ThetaPowerResiduePrimeMeansPNT
```
