# The primitive character spectrum of the prime theta sum

Write $R(p)=S(p)/p-\tfrac12\log p$ for the signed integer sum in Berndt, Bhat, Meyer, Xie and Zaharescu. For every primitive Dirichlet character $\chi$ of conductor $q>1$, the ordinary prime mean
\[
 C_\chi=\lim_{X\to\infty}\frac{1}{\pi(X)}\sum_{p\le X}\chi(p)R(p)
\]
exists. It is nonzero exactly when $q$ is odd and $\chi(-1)=-1$. The convention here uses $\chi(p)$ in the mean. A Fourier coefficient defined using the complex conjugate corresponds to $C_{\bar\chi}$. The principal coefficient is the previously computed mean $B$. [Character classification](ThetaPrimitiveSpectrum.lean) · [Principal mean](NATURAL-PRIME-MEAN.md) · [Pinned definition of $S$ and prime conjectures](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean)

For every positive $m$ with $9\nmid m$ and every real function $g$ on residues modulo $m$, eventually
\[
 \frac{1}{\pi(X)}\sum_{p\le X}|R(p)-g(p\bmod m)|>\frac1{32}.
\]
This includes **every squarefree period**. The lower bound is independent of $m$ and $g$; the threshold in $X$ may depend on both. The proof exhibits a primitive sextic character of modulus nine. Its parity transform has norm $4$, its $L$-value has real part greater than $1/2$, and its local factor at two has norm $\sqrt3/2$. Together these give $|C_\chi|\ge 4|L(1,\chi)|(\sqrt3/2)/54>1/32$. A character whose conductor fails to divide $m$ annihilates every mod-$m$ test in the prime mean. [Modulus-nine certificate](ThetaSexticNine.lean) · [Missing-conductor orthogonality](ThetaPrimitiveTwist.lean) · [Transfer to absolute error](ThetaPrimitiveSpectrum.lean)

## Coefficient formula

For odd $q$ and odd primitive $\chi$, let $\tau(\bar\chi)$ be the Gauss sum with additive character $a\mapsto e^{2\pi i a/q}$. Then
\[
 C_\chi =
 \frac{i(4\bar\chi(2)-2)\,\tau(\bar\chi)L(1,\chi)^2(1-\chi(2)/2)}
 {\pi q\varphi(q)}
 \prod_{\ell\ {\rm prime}}\left(1+\frac{b_\ell}{\ell^2-1}\right).
\]
Here $b_2=0$, $b_\ell=1$ at odd primes dividing $q$, and for the remaining primes
\[
 b_\ell=(1-\bar\chi(\ell))(1-\chi(\ell)/\ell)\frac{\ell}{\ell-1}.
\]
The product converges absolutely and its norm is at least one. Indeed each $b_\ell$ has nonnegative real part, and the associated multiplicative series has an absolutely summable majorant. This proof works for nonreal characters. [Euler product](ThetaDirichletEuler.lean) · [Weights on multiples of the conductor](ThetaConductorMultiples.lean) · [Closed form](ThetaPrimitiveSpectrum.lean)

The finite residue average kills rows whose denominator is missing the primitive conductor. The remaining odd rows have denominators $d=qn$ and their character transforms factor by the primes dividing $n$. The real and imaginary projections pass to the prime mean using the previous finite-row approximation. Even conductors therefore give zero. [Row transforms](ThetaDirichletRows.lean) · [Projection of complex means](ThetaDirichletMeans.lean)

For odd $q$, set $M(\psi)=\sum_{a=0}^{q-1}a\psi(a)$ and $P(\psi)=\sum_{a=0}^{q-1}(-1)^{a+1}\psi(a)$. Doubling residues gives $qP(\psi)=(4\psi(2)-2)M(\psi)$ for nonprincipal $\psi$. Reflection kills the first moment for even $\psi$. For odd primitive $\psi$, the finite Gauss transform and the radial limit of the logarithm give $\tau(\psi)L(1,\bar\psi)=-i\pi M(\psi)/q$. Nonvanishing of $L(1,\chi)$ and of the primitive Gauss sum proves the support criterion. [First moment and parity](ThetaPrimitiveParity.lean) · [Logarithmic radial argument](ThetaQuadraticExcess.lean)

## Source comparison and replay

The paper conjectures pointwise positivity and growth and studies congruences for $S(p)$. The spectrum above concerns normalized prime averages of the same integer sum. The DeepMind reduction and the linked OMA entries address remainder estimates and finite ranges. Guo and Zhang's Hardy and Kloosterman identities use character expansions at a fixed denominator. Here the tested character has fixed conductor and the denominator prime tends to infinity. The finite Gauss and Dirichlet identities in the derivation are classical. [Original paper, section 3](https://arxiv.org/pdf/2501.03234v3#page=4) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA reduction](https://github.com/lefttosolve2/open-math-agents/pull/22818) · [OMA finite verification](https://github.com/lefttosolve2/open-math-agents/pull/18042) · [Left to Solve feed](https://lefttosolve.com/api/solved) · [Guo and Zhang](https://dml.cz/dmlcz/141636)

The notebook theorems take the fixed-progression prime number theorem as an explicit input. The module below uses the pinned proof of that theorem to remove the input. Save it as `ThetaPrimitiveSpectrumPNT.lean` on the joint replay path and run `leanchecker -v ThetaPrimitiveSpectrumPNT`. Its three declarations report only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the derivation and verification. [Progression PNT source and replay](NATURAL-PRIME-MEAN.md#joint-lean-replay)

```lean
import ThetaPrimitiveSpectrum
import ThetaPNTCorollaries

/-! Unconditional prime-average statements from the pinned prime number theorem in progressions. -/
namespace Arxiv.«2501.03234».ThetaPrimitiveSpectrumPNT

open Filter Topology Complex DirichletCharacter ThetaDirichletRows ThetaNaturalPrimeMeans
open ThetaPeriodMeans ThetaPrimitiveSpectrum

/-- Full support criterion for the nonprincipal primitive twists of the original theta sum. -/
theorem primitive_spectrum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 1 < q) :
    Tendsto (primeMeanC (fun p => symbol χ p * ((S p : ℝ) / p - Real.log p / 2 : ℝ))) atTop
      (𝓝 (if _root_.Odd q then coefficient χ else 0)) ∧
    ((if _root_.Odd q then coefficient χ else 0) ≠ 0 ↔ _root_.Odd q ∧ χ.Odd) :=
  spectrum χ hχ hq ThetaPNTCorollaries.progression_mangoldt

/-- Any period missing the second ternary digit has a uniform prime mean absolute error. -/
theorem nine_gap {m : ℕ} [NeZero m] (hm : ¬ 9 ∣ m) {g : ℕ → ℝ} (hg : OnMod m g) :
    ∀ᶠ X in atTop, 1 / 32 < primeMean (fun p => |(S p : ℝ) / p - Real.log p / 2 - g p|) X :=
  nine_obstruction ThetaPNTCorollaries.progression_mangoldt hm hg

theorem squarefree_gap {m : ℕ} [NeZero m] (hm : Squarefree m) {g : ℕ → ℝ} (hg : OnMod m g) :
    ∀ᶠ X in atTop, 1 / 32 < primeMean (fun p => |(S p : ℝ) / p - Real.log p / 2 - g p|) X :=
  squarefree_obstruction ThetaPNTCorollaries.progression_mangoldt hm hg

#print axioms primitive_spectrum
#print axioms nine_gap
#print axioms squarefree_gap
end Arxiv.«2501.03234».ThetaPrimitiveSpectrumPNT
```
