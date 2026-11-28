import ThetaProgressionProjection

/-! Opposite unit classes have opposite centered conditional means. -/
namespace Arxiv.«2501.03234».ThetaOppositeMeans
open Finset Filter Topology Complex DirichletCharacter ThetaPrimitiveSpectrum ThetaNaturalPrimeMeans
open ThetaLevelCoefficients ThetaDirichletRows ThetaFiniteProjection ThetaProgressionProjection
open scoped ComplexConjugate
noncomputable section

private lemma odd_of_value {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m)
    (hv : value χ≠0) (hAP : ProgressionMangoldt) : χ.Odd := by
  by_cases hχ : χ=1
  · simp [value,hχ] at hv
  have hq : 1<χ.conductor := by
    have hp := χ.conductor_ne_zero
    have hn := mt (eq_one_iff_conductor_eq_one (χ:=χ)).mpr hχ
    omega
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have H := (ThetaPrimitiveSpectrum.spectrum χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hq hAP).2
  simp only [value,if_neg hχ] at hv
  have H' := (H.mp hv).2
  have h := χ.primitiveCharacter_apply_of_isCoprime (a:=(-1:ℤ)) ⟨-1,0,by ring⟩
  change χ (-1) = -1
  change χ.primitiveCharacter (-1) = -1 at H'
  simpa using h.symm.trans (by simpa using H')

theorem reflection {m r s : ℕ} [NeZero m] (he : (s:ZMod m)=-(r:ZMod m))
    (hAP : ProgressionMangoldt) : predictor m s = -predictor m r := by
  suffices H : model (value (m:=m)) s = -model (value (m:=m)) r by
    simpa only [predictor,neg_re] using congrArg Complex.re H
  unfold model
  rw [←sum_neg_distrib]
  apply sum_congr rfl
  intro χ _
  by_cases h : value χ=0
  · simp [h]
  · have ho := odd_of_value χ h hAP
    simp only [symbol,he,ho.eval_neg,map_neg,mul_neg]

end
end Arxiv.«2501.03234».ThetaOppositeMeans
#print axioms Arxiv.«2501.03234».ThetaOppositeMeans.reflection
