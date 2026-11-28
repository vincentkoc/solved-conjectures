import ThetaHighAngularEnergy

/-! The cubic energy fraction is uniform in the choice of projection axis. -/

namespace Arxiv.«2501.03234».ThetaRotatedEnergy
open Filter Finset Complex Real DirichletCharacter ThetaPointwiseCubic ThetaPointwiseCutoff
open ThetaRealCharacterMoment ThetaSignedCubicMass ThetaCubicEnergy ThetaCubicEnergyLimit ThetaHighAngularEnergy
open scoped ComplexConjugate
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def projected (D : Finset (DirichletCharacter ℂ p)) (z : ℂ) : ℝ :=
  ∑ χ ∈ D, ((z*cubic χ).re)^2

private lemma cubic_inv (χ : DirichletCharacter ℂ p) : cubic χ⁻¹=conj (cubic χ) := by
  simp only [cubic, inverse_half,map_mul,map_pow,conj_conj]

private lemma mixed_zero (D : Finset (DirichletCharacter ℂ p)) (hD : ∀ χ∈D,χ⁻¹∈D) :
    ∑ χ ∈ D,(cubic χ).re*(cubic χ).im = 0 := by
  let f := fun χ : DirichletCharacter ℂ p => (cubic χ).re*(cubic χ).im
  have h : ∑ χ∈D,f χ = ∑ χ∈D,f χ⁻¹ := by
    apply sum_nbij' (fun χ => χ⁻¹) (fun χ => χ⁻¹) hD hD <;> simp
  have hflip (χ : DirichletCharacter ℂ p) : f χ⁻¹ = -f χ := by simp [f,cubic_inv]
  simp_rw [hflip,sum_neg_distrib] at h
  change (∑ χ∈D,f χ)=0
  linarith

theorem rotated {D : Finset (DirichletCharacter ℂ p)} (hD : ∀ χ∈D,χ⁻¹∈D)
    {z : ℂ} (hz : ‖z‖=1) (ht : 0<total D) :
    |projected D z / total D-1/2| ≤ |realEnergy D / total D-1/2| := by
  have hnorm : z.re^2+z.im^2=1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply,hz] at h
    linarith
  have hpr : projected D z=z.re^2*realEnergy D+z.im^2*imagEnergy D := by
    unfold projected realEnergy imagEnergy
    have hp (χ : DirichletCharacter ℂ p) :
        ((z*cubic χ).re)^2 = z.re^2*((cubic χ).re)^2+z.im^2*((cubic χ).im)^2-
          (2*z.re*z.im)*((cubic χ).re*(cubic χ).im) := by rw [mul_re]; ring
    simp_rw [hp,sum_sub_distrib,sum_add_distrib,←mul_sum,mixed_zero D hD,mul_zero,sub_zero]
  have hi := energy_add D
  have hsplit : projected D z/total D-1/2=(z.re^2-z.im^2)*(realEnergy D/total D-1/2) := by
    rw [hpr]
    field_simp
    linear_combination (2*z.im^2)*hi+(total D)*hnorm
  rw [hsplit,abs_mul]
  apply mul_le_of_le_one_left (abs_nonneg _)
  rw [abs_le]
  constructor <;> nlinarith only [hnorm,sq_nonneg z.re,sq_nonneg z.im]

theorem all_directions (hp : p%2=1) {z : ℂ} (hz : ‖z‖=1) :
    |projected (nonprincipal p) z/total (nonprincipal p)-1/2| ≤
      1536*(harmonic (p/2):ℝ)^6/(p:ℝ)^(1/4:ℝ) := by
  have hh := lower hp
  have ht : 0<(p.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (Fact.out : p.Prime).pos
  apply (rotated _ hz (lt_of_lt_of_le (by positivity) hh)).trans (relative_error hp)
  intro χ h
  simpa [nonprincipal] using h

theorem high_directions {ε η : ℝ} (he : 0<ε) (hη : 0<η) :
    ∀ᶠ p : ℕ in atTop,∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ z : ℂ, ‖z‖=1 → |projected (large p ε) z/total (large p ε)-1/2|<η := by
  filter_upwards [high_fraction he hη, high_fraction he (by norm_num : (0:ℝ)<1/4)] with p H H'
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  intro z hz
  have ht : 0<total (large p ε) := by
    have hn : 0≤total (large p ε) := sum_nonneg (fun _ _ => sq_nonneg _)
    rcases hn.eq_or_lt with he|h
    · have := H' hp ho
      rw [←he] at this
      norm_num at this
    · exact h
  apply (rotated _ hz ht).trans_lt (H hp ho)
  intro χ h
  simpa [large,nonprincipal,orderOf_inv] using h

#print axioms all_directions
#print axioms high_directions
end
end Arxiv.«2501.03234».ThetaRotatedEnergy
