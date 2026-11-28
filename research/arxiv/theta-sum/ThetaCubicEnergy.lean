import ThetaAngularMoments

/-! An explicit lower bound for the radial sixth moment of the theta coefficients. -/

namespace Arxiv.«2501.03234».ThetaCubicEnergy
open Finset Complex Real DirichletCharacter ThetaFourier ThetaPointwiseCubic ThetaPointwiseCutoff
open ThetaRealCharacterMoment ThetaAngularMoments
open scoped ComplexConjugate
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def total (D : Finset (DirichletCharacter ℂ p)) : ℝ := ∑ χ∈D, ‖cubic χ‖^2
def realEnergy (D : Finset (DirichletCharacter ℂ p)) : ℝ := ∑ χ∈D, ((cubic χ).re)^2
def imagEnergy (D : Finset (DirichletCharacter ℂ p)) : ℝ := ∑ χ∈D, ((cubic χ).im)^2

lemma energy_add (D : Finset (DirichletCharacter ℂ p)) : realEnergy D+imagEnergy D=total D := by
  rw [realEnergy,imagEnergy,total,←sum_add_distrib]
  apply sum_congr rfl
  intro χ _
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

lemma norm_moment (hp : p%2=1) :
    ∑ χ∈nonprincipal p,‖halfSum χ‖^2 = (p.totient:ℝ)^2/4 := by
  have h := congrArg Complex.re (norm_square_sum (p:=p))
  simp_rw [inverse_half, mul_conj,Complex.normSq_eq_norm_sq] at h
  simp only [Complex.re_sum, ofReal_re] at h
  have h1 : halfSum (1 : DirichletCharacter ℂ p)=(odds p).card := by
    unfold halfSum
    exact (sum_congr rfl (fun a ha => MulChar.one_apply (unit_odd ha))).trans (by simp)
  have hc : (p.totient:ℝ)=2*(odds p).card := by
    rw [Nat.totient_prime (Fact.out : p.Prime),card_odds hp]
    exact_mod_cast (show p-1=2*(p/2) by omega)
  have hf : nonprincipal p=univ.erase (1 : DirichletCharacter ℂ p) := by ext; simp [nonprincipal]
  rw [← sum_erase_add _ _ (mem_univ (1 : DirichletCharacter ℂ p)), h1,Complex.norm_natCast] at h
  rw [show ((p.totient:ℂ)*(odds p).card).re = (p.totient:ℝ)*(odds p).card by simp] at h
  rw [hf,hc]
  rw [hc] at h
  linarith

theorem lower (hp : p%2=1) : (p.totient:ℝ)^4/64 ≤ total (nonprincipal p) := by
  let m := (p.totient:ℝ)/4
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have card : ((nonprincipal p).card:ℝ) ≤ p.totient := by
    exact_mod_cast (show (nonprincipal p).card ≤ p.totient from (card_le_univ _).trans_eq (by
      simpa only [Nat.card_eq_fintype_card] using card_eq_totient_of_hasEnoughRootsOfUnity ℂ p))
  have fac (χ : DirichletCharacter ℂ p) :
      3*m^2*‖halfSum χ‖^2-2*m^3 ≤ ‖cubic χ‖^2 := by
    rw [cubic,inverse_half,norm_mul,norm_pow,norm_conj]
    nlinarith only [mul_nonneg (sq_nonneg (‖halfSum χ‖^2-m)) (show 0≤‖halfSum χ‖^2+2*m by positivity)]
  have hs := sum_le_sum (s:=nonprincipal p) (fun χ _ => fac χ)
  rw [sum_sub_distrib,←mul_sum,norm_moment hp,sum_const,nsmul_eq_mul] at hs
  have hc := mul_le_mul_of_nonneg_right card (show 0≤2*m^3 by positivity)
  change _ ≤ total (nonprincipal p) at hs
  dsimp [m] at hc hs
  linarith

theorem fraction_error (hp : p%2=1) :
    |realEnergy (nonprincipal p)/total (nonprincipal p) - 1/2| ≤
      32*((p:ℝ)^2*((p.totient:ℝ)*(2*(p:ℝ)^(3/4:ℝ))+1)*(harmonic (p/2):ℝ)^6)/(p.totient:ℝ)^4 := by
  let D := nonprincipal p
  have hφ : (0:ℝ)<p.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (Fact.out : p.Prime).pos)
  have hlow := lower hp
  have ht : 0<total D := lt_of_lt_of_le (by positivity) hlow
  have hi := energy_add D
  have e : realEnergy D/total D-1/2 = (realEnergy D-imagEnergy D)/(2*total D) := by
    field_simp
    linarith
  change |realEnergy D/total D - 1/2| ≤ _
  rw [e,abs_div,abs_of_pos (by positivity : 0<2*total D)]
  have err := cubic_energy_error hp
  change |realEnergy D-imagEnergy D|≤_ at err
  have hE : 0≤(p:ℝ)^2*((p.totient:ℝ)*(2*(p:ℝ)^(3/4:ℝ))+1)*(harmonic (p/2):ℝ)^6 := by positivity
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  apply (mul_le_mul_of_nonneg_right err (by positivity)).trans
  have hden : (p.totient:ℝ)^4≤64*total D := by linarith
  nlinarith only [mul_le_mul_of_nonneg_left hden hE]

#print axioms lower
#print axioms fraction_error
end
end Arxiv.«2501.03234».ThetaCubicEnergy
