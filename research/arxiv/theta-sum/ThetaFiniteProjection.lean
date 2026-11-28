import ThetaLevelCoefficients

/-! Finite Fourier projections of the theta residual in empirical prime mean square. -/
namespace Arxiv.«2501.03234».ThetaFiniteProjection
open Finset Filter Topology Complex DirichletCharacter ThetaPrimitiveSpectrum ThetaNaturalPrimeMeans
open ThetaLevelCoefficients ThetaDirichletRows
open scoped ComplexConjugate
noncomputable section

/-- A finite character series at the chosen level. -/
def model {m : ℕ} [NeZero m] (b : DirichletCharacter ℂ m → ℂ) (p : ℕ) : ℂ :=
  ∑ χ,b χ*conj (symbol χ p)

def energy (m : ℕ) [NeZero m] : ℝ := ∑ χ : DirichletCharacter ℂ m, ‖value χ‖^2

private theorem meanC_sum {ι : Type*} [Fintype ι] (f : ι → ℕ → ℂ) (X : ℕ) :
    primeMeanC (fun p => ∑ i,f i p) X=∑ i,primeMeanC (f i) X := by
  simp only [primeMeanC,←sum_div]
  rw [sum_comm]

private theorem meanC_mul (f : ℕ → ℂ) (b : ℂ) (X : ℕ) :
    primeMeanC (fun p => f p*b) X=primeMeanC f X*b := by
  simp only [primeMeanC,←sum_mul]
  ring

/-- Pair a summand of known character means with any finite periodic Fourier series. -/
theorem pairing {m : ℕ} [NeZero m] (f : ℕ → ℂ) (a b : DirichletCharacter ℂ m → ℂ)
    (h : ∀ χ, Tendsto (primeMeanC (fun p => f p*symbol χ p)) atTop (𝓝 (a χ))) :
    Tendsto (primeMeanC (fun p => f p*conj (model b p))) atTop (𝓝 (∑ χ,a χ*conj (b χ))) := by
  have H := tendsto_finsetSum univ fun χ _ => (h χ).mul_const (conj (b χ))
  apply H.congr'
  filter_upwards with X
  have he (p) : f p*conj (model b p)=∑ χ,(f p*symbol χ p)*conj (b χ) := by
    simp only [model,map_sum,map_mul,conj_conj,mul_sum]
    apply sum_congr rfl
    intro χ _
    ring
  simp_rw [he]
  rw [meanC_sum]
  simp only [meanC_mul]

theorem model_twist {m : ℕ} [NeZero m] (b : DirichletCharacter ℂ m → ℂ)
    (ψ : DirichletCharacter ℂ m) (hAP : ProgressionMangoldt) :
    Tendsto (primeMeanC (fun p => model b p*symbol ψ p)) atTop (𝓝 (b ψ)) := by
  classical
  have h (χ : DirichletCharacter ℂ m) := (character_mean (χ⁻¹*ψ) hAP).mul_const (b χ)
  have H := tendsto_finsetSum univ fun χ _ => h χ
  have heq (χ : DirichletCharacter ℂ m) : χ⁻¹*ψ=1 ↔ χ=ψ := by rw [inv_mul_eq_one]
  simp_rw [heq] at H
  simp only [ite_mul,one_mul,zero_mul,sum_ite_eq',mem_univ,if_true] at H
  apply H.congr'
  filter_upwards with X
  have he (p) : model b p*symbol ψ p=∑ χ,symbol (χ⁻¹*ψ) p*b χ := by
    simp only [model,sum_mul,symbol,MulChar.mul_apply]
    apply sum_congr rfl
    intro χ _
    rw [← MulChar.star_apply']
    change _ = (conj _ * _)*_
    ring
  simp_rw [he]
  rw [meanC_sum]
  simp only [meanC_mul]

theorem model_square {m : ℕ} [NeZero m] (b : DirichletCharacter ℂ m → ℂ) (hAP : ProgressionMangoldt) :
    Tendsto (primeMean (fun p => ‖model b p‖^2)) atTop (𝓝 (∑ χ,‖b χ‖^2)) := by
  have H := continuous_re.continuousAt.tendsto.comp (pairing (model b) b b (fun χ => model_twist b χ hAP))
  simpa only [Function.comp_def,meanC_re,mul_conj,ofReal_re,re_sum,Complex.sq_norm] using H

/-- Sharp mean-square error for arbitrary coefficients of a fixed-period model. -/
theorem squared_error {m : ℕ} [NeZero m] (b : DirichletCharacter ℂ m → ℂ) {V : ℝ}
    (hV : Tendsto (primeMean (fun p => (centered p)^2)) atTop (𝓝 V))
    (hAP : ProgressionMangoldt) :
    Tendsto (primeMean (fun p => ‖(centered p:ℂ)-model b p‖^2)) atTop
      (𝓝 (V-energy m+∑ χ,‖value χ-b χ‖^2)) := by
  have h := pairing (fun p => (centered p:ℂ)) value b (fun χ => by
    simpa only [mul_comm (centered _:ℂ)] using coefficient_limit χ hAP)
  have hcross := continuous_re.continuousAt.tendsto.comp h
  simp only [Function.comp_def,meanC_re,re_sum] at hcross
  have H := (hV.add (model_square b hAP)).sub (hcross.const_mul 2)
  have hz : V+∑ χ,‖b χ‖^2-2*∑ χ,(value χ*conj (b χ)).re = V-energy m+∑ χ,‖value χ-b χ‖^2 := by
    simp only [energy,Complex.sq_norm,normSq_sub,sum_sub_distrib,sum_add_distrib,←mul_sum]
    ring
  rw [hz] at H
  apply H.congr'
  filter_upwards with X
  simp only [primeMean,Complex.sq_norm,normSq_sub,normSq_ofReal,←sub_div,←add_div,←mul_div_assoc,
    mul_sum,←sum_sub_distrib,←sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro p _
  ring

theorem energy_le {m : ℕ} [NeZero m] {V : ℝ}
    (hV : Tendsto (primeMean (fun p => (centered p)^2)) atTop (𝓝 V)) (hAP : ProgressionMangoldt) :
    energy m ≤ V := by
  have H := squared_error (m:=m) value hV hAP
  simp only [sub_self,norm_zero,zero_pow (by decide : 2≠0),sum_const_zero,add_zero] at H
  exact sub_nonneg.mp (ge_of_tendsto H (.of_forall fun X => div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)))

#print axioms model_twist
#print axioms squared_error
#print axioms energy_le
end
end Arxiv.«2501.03234».ThetaFiniteProjection
