import ThetaRotatedEnergy
import ThetaCubicProportions

/-! A lower second moment for the odd-representative sums in every complex direction. -/
namespace Arxiv.«2501.03234».ThetaDirectionalHalfMoment
open Finset Filter Real Complex DirichletCharacter ThetaPointwiseCubic ThetaPointwiseCutoff
open ThetaRealCharacterMoment ThetaOddInverseCount ThetaCubicEnergy
noncomputable section

theorem covariance {p : ℕ} [Fact p.Prime] (ho : _root_.Odd p) (hp4 : 4≤p)
    (hd : ThetaReciprocalCutoff.discrepancy p≤(p:ℝ)/8) {z : ℂ} (hz : ‖z‖=1) :
    (p:ℝ)^2/32≤∑ χ∈nonprincipal p,((z*halfSum χ).re)^2 := by
  classical
  let D := nonprincipal p
  let A (χ : DirichletCharacter ℂ p) := halfSum χ
  let R := ∑ χ∈D,(A χ).re^2
  let I := ∑ χ∈D,(A χ).im^2
  let φ := (p.totient:ℝ)
  let b := (inverseCount p:ℝ)
  have hmod := Nat.odd_iff.mp ho
  have hprime : p.Prime := Fact.out
  have hφ : φ=(p:ℝ)-1 := by dsimp [φ];rw [Nat.totient_prime hprime,Nat.cast_sub hprime.one_le];norm_num
  have hh : 2*((p/2:ℕ):ℝ)+1=p := by exact_mod_cast (show 2*(p/2)+1=p by omega)
  have hx : 4≤(p:ℝ) := by exact_mod_cast hp4
  have hhalf : (p:ℝ)/2≤φ := by linarith
  obtain ⟨hlo,hhi⟩ := abs_le.mp ((inverse_discrepancy hmod).trans hd)
  change _≤2*b-((p/2:ℕ):ℝ) at hlo
  change 2*b-((p/2:ℕ):ℝ)≤_ at hhi
  have hb : (p:ℝ)/8≤b := by linarith
  have hc : (p:ℝ)/8≤φ/2-b := by linarith
  have hR : 2*R=φ*b := real_second_moment ho
  have hI : R+I=φ^2/4 := by
    apply Eq.trans _ (norm_moment hmod)
    dsimp only [R,I,D,A]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro χ _
    rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    ring
  have hR' : (p:ℝ)^2/32≤R := by
    nlinarith only [hR,mul_le_mul hhalf hb (by positivity : 0≤(p:ℝ)/8) (Nat.cast_nonneg p.totient)]
  have hI' : (p:ℝ)^2/32≤I := by
    nlinarith only [hI,hR,mul_le_mul hhalf hc (by positivity : 0≤(p:ℝ)/8) (Nat.cast_nonneg p.totient)]
  let f (χ : DirichletCharacter ℂ p) := (A χ).re*(A χ).im
  have hinv (χ : DirichletCharacter ℂ p) (hχ : χ∈D) : χ⁻¹∈D := by simpa [D,nonprincipal] using hχ
  have hrot : ∑ χ∈D,f χ=∑ χ∈D,f χ⁻¹ := by
    apply sum_nbij' (fun χ => χ⁻¹) (fun χ => χ⁻¹) hinv hinv <;> simp
  have hflip (χ : DirichletCharacter ℂ p) : f χ⁻¹= -f χ := by simp [f,A,inverse_half]
  simp_rw [hflip,sum_neg_distrib] at hrot
  have hzero : ∑ χ∈D,(A χ).re*(A χ).im=0 := by change ∑ χ∈D,f χ=0;linarith only [hrot]
  have hid (χ : DirichletCharacter ℂ p) : ((z*A χ).re)^2=
    z.re^2*(A χ).re^2+z.im^2*(A χ).im^2-(2*z.re*z.im)*((A χ).re*(A χ).im) := by rw [mul_re];ring
  have hnorm : z.re^2+z.im^2=1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply,hz] at h
    linarith
  change _ ≤ ∑ χ∈D,((z*A χ).re)^2
  simp_rw [hid,sum_sub_distrib,sum_add_distrib,←mul_sum,hzero,mul_zero,sub_zero]
  change _≤z.re^2*R+z.im^2*I
  nlinarith only [mul_le_mul_of_nonneg_left hR' (sq_nonneg z.re),
    mul_le_mul_of_nonneg_left hI' (sq_nonneg z.im),congrArg (fun a : ℝ => a*(p:ℝ)^2/32) hnorm]

#print axioms covariance
end
end Arxiv.«2501.03234».ThetaDirectionalHalfMoment
