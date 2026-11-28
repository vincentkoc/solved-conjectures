import ThetaAngularTests

/-! Quantitative control of the second angular harmonic of every fixed radial moment. -/

namespace Arxiv.«2501.03234».ThetaAngularMoments
open Finset Complex Real DirichletCharacter ThetaPointwiseCubic ThetaPointwiseCutoff
open ThetaPointwiseCompletion ThetaHalfSpectrum ThetaGaussAngularKernel ThetaAngularTests
open ThetaCharacterFourthMoment (U)
open scoped ComplexConjugate
noncomputable section
variable {p : ℕ} [Fact p.Prime]

lemma variation_le (hp : p%2=1) : variation p ≤ harmonic (p/2) := by
  have hpp : 0<(p:ℝ) := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  unfold variation freq
  simp_rw [norm_div,Complex.norm_natCast]
  rw [← sum_div,div_le_iff₀ hpp]
  have he : (∑ x : U p, ‖ThetaFourier.amp (ThetaFourier.odds p) (-(x:ZMod p))‖) =
      ThetaFourier.mass (ThetaFourier.odds p) := by
    apply sum_bij (fun (x : U p) _ => -(x:ZMod p))
    · intro x _; simp [x.ne_zero]
    · intro a _ b _ h; exact Units.ext (neg_injective h)
    · intro y hy
      have h := (mem_erase.mp hy).1
      exact ⟨Units.mk0 (-y) (neg_ne_zero.mpr h),mem_univ _,neg_neg _⟩
    · intros; rfl
  rw [he,mul_comm]
  exact ThetaFourier.mass_odds hp

private lemma tau_square {χ : DirichletCharacter ℂ p} (hn : χ≠1) :
    tau χ * conj (tau χ) = (p:ℂ) := by
  rw [mul_conj,Complex.normSq_eq_norm_sq,show ‖tau χ‖=Real.sqrt p from
    ThetaConductorDecay.gauss_norm χ (primitive hn),Real.sq_sqrt (Nat.cast_nonneg p)]
  simp

theorem angular_bound (hp : p%2=1) (r : ℕ) :
    ‖∑ χ ∈ nonprincipal p,(halfSum χ)^(r+2)*(conj (halfSum χ))^r‖ ≤
      (p:ℝ)^r*((p.totient:ℝ)*(2*(p:ℝ)^(3/4:ℝ))+1)*(harmonic (p/2):ℝ)^(2*r+2) := by
  let D := (p.totient:ℝ)*(2*(p:ℝ)^(3/4:ℝ))+1
  have hD : 0≤D := by dsimp [D]; positivity
  have ht : TwistedBound (fun χ : DirichletCharacter ℂ p => (tau χ)^2) D := twisted_bound
  have h := product_tests ht (r+2) r (1:U p)
  simp only [Units.val_one,map_one,mul_one] at h
  have e (χ : DirichletCharacter ℂ p) (hn : χ∈nonprincipal p) :
      (halfSum χ)^(r+2)*(conj (halfSum χ))^r =
        (p:ℂ)^r*((tau χ)^2*(F χ)^(r+2)*(conj (F χ))^r) := by
    have hn' := (mem_filter.mp hn).2
    have hh : halfSum χ=tau χ*F χ := complete hn'
    rw [hh,map_mul,mul_pow,mul_pow,←tau_square hn',mul_pow,pow_add (tau χ)]
    ring
  rw [sum_congr rfl e,← mul_sum,norm_mul,norm_pow,Complex.norm_natCast]
  calc
    _ ≤ (p:ℝ)^r*(D*(variation p)^((r+2)+r)) := mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ _ := by
      rw [show r+2+r=2*r+2 by omega,mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hD
      exact pow_le_pow_left₀ (sum_nonneg (fun _ _ => norm_nonneg _)) (variation_le hp) _

theorem cubic_energy_error (hp : p%2=1) :
    |(∑ χ ∈ nonprincipal p,((cubic χ).re)^2)-(∑ χ ∈ nonprincipal p,((cubic χ).im)^2)| ≤
      (p:ℝ)^2*((p.totient:ℝ)*(2*(p:ℝ)^(3/4:ℝ))+1)*(harmonic (p/2):ℝ)^6 := by
  have h := angular_bound hp 2
  have he (χ : DirichletCharacter ℂ p) : (halfSum χ)^(2+2)*(conj (halfSum χ))^2=(cubic χ)^2 := by
    rw [cubic,ThetaRealCharacterMoment.inverse_half]
    ring
  simp_rw [he] at h
  have hr : (∑ χ ∈ nonprincipal p,(cubic χ)^2).re =
      (∑ χ ∈ nonprincipal p,((cubic χ).re)^2)-(∑ χ ∈ nonprincipal p,((cubic χ).im)^2) := by
    simp only [re_sum, pow_two, mul_re,sum_sub_distrib]
  rw [←hr]
  exact (abs_re_le_norm _).trans h

#print axioms angular_bound
#print axioms cubic_energy_error
end
end Arxiv.«2501.03234».ThetaAngularMoments
