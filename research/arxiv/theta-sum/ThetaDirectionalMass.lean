import ThetaDirectionalHalfMoment

/-! Absolute and positive masses of the cubic character coefficients in each direction. -/
namespace Arxiv.«2501.03234».ThetaDirectionalMass
open Finset Filter Real Complex DirichletCharacter ThetaPointwiseCubic ThetaPointwiseCutoff
open ThetaAbsoluteCubicMass ThetaRealCharacterMoment
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def projection (z : ℂ) (χ : DirichletCharacter ℂ p) : ℝ := (z*cubic χ).re

theorem projection_eq (z : ℂ) (χ : DirichletCharacter ℂ p) :
    projection z χ = ‖halfSum χ‖^2*(z*halfSum χ).re := by
  rw [projection,cubic,inverse_half,pow_two,mul_assoc,mul_conj,Complex.normSq_eq_norm_sq,
    ←mul_assoc,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,mul_comm]

private theorem threshold {z : ℂ} (hz : ‖z‖=1) (χ : DirichletCharacter ℂ p) {T : ℝ} (hT : 0≤T) :
    T*((z*halfSum χ).re)^2 ≤ |projection z χ|+T^3 := by
  rw [projection_eq,abs_mul,abs_of_nonneg (sq_nonneg _)]
  let x := |(z*halfSum χ).re|
  have hx : 0≤x := abs_nonneg _
  have hn : x≤‖halfSum χ‖ := (abs_re_le_norm _).trans_eq (by rw [norm_mul,hz,one_mul])
  have h2 : x^2=((z*halfSum χ).re)^2 := sq_abs _
  rw [←h2]
  change T*x^2 ≤ ‖halfSum χ‖^2*x+T^3
  rcases le_total x T with h|h
  · have h' := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx h 2) hT
    nlinarith only [h',mul_nonneg (sq_nonneg ‖halfSum χ‖) hx]
  · have h' := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx hn 2) hx
    nlinarith only [h',mul_le_mul_of_nonneg_right h (sq_nonneg x),pow_nonneg hT 3]

theorem absolute_lower (ho : _root_.Odd p) (hp4 : 4≤p)
    (hd : ThetaReciprocalCutoff.discrepancy p≤(p:ℝ)/8) {z : ℂ} (hz : ‖z‖=1) :
    scale p/512 ≤ ∑ χ∈nonprincipal p,|projection z χ| := by
  let T := Real.sqrt p/8
  have hx : 0≤(p:ℝ) := Nat.cast_nonneg _
  have hT : 0≤T := by dsimp [T]; positivity
  have hs := sum_le_sum (s:=nonprincipal p) (fun χ _ => threshold hz χ hT)
  rw [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul] at hs
  have hc := ThetaCubicProportions.card_le (nonprincipal p)
  have hsm := ThetaDirectionalHalfMoment.covariance ho hp4 hd hz
  have hs' := (mul_le_mul_of_nonneg_left hsm hT).trans hs
  have hupper := mul_le_mul_of_nonneg_right hc (pow_nonneg hT 3)
  dsimp [T,scale] at *
  nlinarith only [hs',hupper,congrArg (fun x : ℝ => x*(p:ℝ)*Real.sqrt p) (Real.sq_sqrt hx)]

theorem signed (ho : _root_.Odd p) {z : ℂ} (hz : ‖z‖=1) :
    |∑ χ∈nonprincipal p,projection z χ| ≤ |∑ χ∈nonprincipal p,(cubic χ).re| := by
  have hi := congrArg Complex.im (expansion (p:=p) ho)
  simp only [Complex.mul_im,Complex.natCast_im,Complex.intCast_im,mul_zero,zero_mul,add_zero,
    Complex.im_sum] at hi
  norm_num at hi
  have hzero : ∑ χ∈nonprincipal p,(cubic χ).im=0 := hi
  simp only [projection,mul_re,sum_sub_distrib,←mul_sum,hzero,mul_zero,sub_zero,abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) ((abs_re_le_norm z).trans hz.le)

theorem positive_lower :
    ∀ᶠ p : ℕ in atTop,∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ z : ℂ, ‖z‖=1 → scale p/2048 ≤ ∑ χ∈nonprincipal p,max (projection z χ) 0 := by
  filter_upwards [ThetaOddInverseCount.discrepancy_small,eventually_ge_atTop 4,
    ThetaSignedCubicMass.signed_bound (by norm_num : (0:ℝ)<1/8192)] with p hd hp4 hs
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  intro z hz
  have hA := absolute_lower ho hp4 hd hz
  have hS := (abs_le.mp ((signed ho hz).trans (hs hp ho))).1
  have point (v : ℝ) : |v|+v=2*max v 0 := by
    rcases le_total v 0 with hv|hv
    · rw [abs_of_nonpos hv,max_eq_right hv]; ring
    · rw [abs_of_nonneg hv,max_eq_left hv]; ring
  have hh := sum_congr (s₁:=nonprincipal p) rfl (fun χ _ => point (projection z χ))
  rw [sum_add_distrib,←mul_sum] at hh
  have hscale : 0 ≤ scale p := by unfold scale; positivity
  linarith only [hA,hS,hh,hscale]

#print axioms absolute_lower
#print axioms signed
#print axioms positive_lower
end
end Arxiv.«2501.03234».ThetaDirectionalMass
