# Exact order of the conductor tail

Write \(R(p)=S(p)/p-\tfrac12\log p\), let \(V\) be its limiting empirical variance over primes, and let \(V_{\le Y}\) be the sum of \(|C_\chi|^2\) over all primitive Dirichlet characters of conductor at most \(Y\). There is an absolute \(c>0\) such that every sufficiently large integer \(Y\) satisfies
\[
 c \le Y(V-V_{\le Y}) \le 449280 .
\]
In particular a conductor cutoff cannot have error \(o(1/Y)\). This concerns the tail of the full limiting variance. It gives neither a limiting value for \(Y(V-V_{\le Y})\) nor an asymptotic for an individual coefficient. [Matching cutoff](ThetaSharpConductorTail.lean) · [Parseval expansion and upper bound](SPECTRAL-VARIANCE.md) · [Pinned integer sum](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean)

## Why enough conductors contribute

For \(q\ge5\), odd-character orthogonality leaves two residues in a complete harmonic block. Their difference is \(1/(qk+1)-1/(qk+q-1)>0\). Taking eight blocks and bounding the remaining harmonic error gives
\[
 \sum_{\chi\bmod q,\ \chi(-1)=-1}\Re L(1,\chi)\ \ge\ \frac{\varphi(q)}4 .
\]
An imprimitive character descends to \(q/p\) for some prime \(p\mid q\). The number of imprimitive characters is at most \(\varphi(q)\delta(q)\), where \(\delta(q)=\sum_{p\mid q}1/(p-1)\). The uniform fourth moment at one bounds the first-moment contribution of these characters. If \(\delta(q)\le1/1024\), the surviving primitive odd characters satisfy \(\sum |L(1,\chi)|^4\ge\varphi(q)/65536\). At an odd conductor the coefficient magnitude identity then gives at least \(1/(1048576q^2)\) of variance in that single layer. [Odd first moment](ThetaOddCharacterMean.lean) · [Imprimitive count](ThetaPrimitiveCount.lean) · [Primitive fourth moment](ThetaPrimitiveMomentLower.lean) · [Conductor layer](ThetaConductorLayerLower.lean)

Fix \(T=16384\) and \(M=T!\). For \(Y\le k<2Y\), every prime dividing \(Mk+1\) exceeds \(T\); at most \(2Y/p+1\) indices satisfy the corresponding congruence. Summing over primes gives
\[
 \sum_{Y\le k<2Y}\delta(Mk+1)
 \le 2Y/T+2\bigl(1+\log(2MY+1)\bigr).
\]
Consequently at least \(Y/2\) indices eventually satisfy \(\delta(Mk+1)\le1/1024\). Their odd conductors are distinct, exceed \(Y\), and are bounded by \((2M+1)Y\). Adding their masses proves the lower bound with \(c=1/(2097152(2M+1)^2)\). The argument establishes the order of decay; the lower constant is very small. [Counting conductors](ThetaRoughConductors.lean) · [Assembly](ThetaSharpConductorTail.lean)

## Source comparison and replay

The original paper and pinned formal conjectures concern \(S(p)\) pointwise. The DeepMind issue and OMA submissions reduce those questions to remainder and finite harmonic estimates. The fourth and first moments here run over characters at each fixed conductor; their contribution to the original prime average is supplied by the primitive coefficient identity. The pointwise conjectures remain open. [Berndt, Bhat, Meyer, Xie and Zaharescu](https://arxiv.org/pdf/2501.03234v3#page=4) · [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA harmonic step](https://github.com/lefttosolve2/open-math-agents/pull/22818) · [Left to Solve](https://lefttosolve.com/api/solved) · [Fixed-denominator Hardy identities of Guo and Zhang](https://dml.cz/dmlcz/141636)

The following module uses the pinned fixed-progression prime number theorem to discharge the analytic input. [PNT source and joint replay](NATURAL-PRIME-MEAN.md#joint-lean-replay)

```lean
import ThetaSharpConductorTail
import ThetaPNTCorollaries

/-! Matching upper and lower conductor cutoffs for the empirical prime theta variance. -/
namespace Arxiv.«2501.03234».ThetaSharpConductorTailPNT
open Filter Topology ThetaNaturalPrimeMeans ThetaCharacterPrimeMeans ThetaFullVarianceTail

theorem original_variance_tail :
    ∃ V c : ℝ, 0 < c ∧
      Tendsto (sampleVariance (fun p => (S p : ℝ)/p-Real.log p/2)) atTop (𝓝 V) ∧
      ∀ᶠ Y : ℕ in atTop,
        c ≤ Y*(V-∑ u∈through Y,u.mass) ∧ Y*(V-∑ u∈through Y,u.mass) ≤ 449280 := by
  have hAP : ProgressionMangoldt := ThetaPNTCorollaries.progression_mangoldt
  obtain ⟨_,V,_,_,_,_,hV,hvar⟩ := S_prime_class_statistics hAP
  obtain ⟨c,hc,h⟩ := ThetaSharpConductorTail.sharp hV hAP
  exact ⟨V,c,hc,hvar,h⟩

#print axioms original_variance_tail
end Arxiv.«2501.03234».ThetaSharpConductorTailPNT
```
