import ThetaHalfSpectrum
import ThetaReciprocalCutoff

/-! The second twisted Gauss moment is an elementary Kloosterman sum. -/

namespace Arxiv.«2501.03234».ThetaGaussAngularKernel
open Finset Complex DirichletCharacter ThetaPointwiseCutoff ThetaReciprocalCutoff
open ThetaCharacterFourthMoment (U)
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def tau (χ : DirichletCharacter ℂ p) : ℂ := gaussSum χ ZMod.stdAddChar

private lemma tau_units (χ : DirichletCharacter ℂ p) :
    tau χ = ∑ x : U p, χ (x:ZMod p)*ZMod.stdAddChar (x:ZMod p) := by
  classical
  unfold tau gaussSum
  rw [← sum_erase_add _ _ (mem_univ (0:ZMod p))]
  simp only [MulChar.map_zero,zero_mul,add_zero]
  symm
  apply sum_bij (fun (x : U p) _ => (x:ZMod p))
  · intro x _; simp [x.ne_zero]
  · intro a _ b _ h; exact Units.ext h
  · intro t ht; exact ⟨Units.mk0 t (mem_erase.mp ht).1,mem_univ _,rfl⟩
  · intros; rfl

theorem second (u : U p) :
    ∑ χ : DirichletCharacter ℂ p,(tau χ)^2*χ (u:ZMod p) =
      (p.totient:ℂ)*kloosterman 1 (↑(u⁻¹):ZMod p) := by
  classical
  simp_rw [tau_units, sq, sum_mul, mul_sum]
  simp_rw [sum_comm (s:=(univ:Finset (DirichletCharacter ℂ p))) (t:=(univ:Finset (U p)))]
  unfold kloosterman
  rw [mul_sum]
  apply sum_congr rfl
  intro x _
  have fac (y : U p) (χ : DirichletCharacter ℂ p) :
      χ (x:ZMod p)*ZMod.stdAddChar (x:ZMod p)*(χ (y:ZMod p)*ZMod.stdAddChar (y:ZMod p))*χ (u:ZMod p) =
      ZMod.stdAddChar ((x:ZMod p)+(y:ZMod p))*χ (((x*u)*y:U p):ZMod p) := by
    simp [AddChar.map_add_eq_mul, map_mul]
    ring
  simp only [sum_mul]
  rw [sum_comm]
  simp_rw [fac, ← mul_sum, sum_characters_eq]
  have iff (y : U p) : ((((x*u)*y:U p):ZMod p)=1) ↔ y=(x*u)⁻¹ := by
    rw [← Units.val_one (α:=ZMod p),Units.val_inj]
    constructor
    · intro h; exact eq_inv_of_mul_eq_one_right h
    · rintro rfl; simp
  simp only [iff,mul_ite,mul_zero, Finset.sum_ite_eq', mem_univ, if_true]
  simp only [mul_inv_rev, Units.val_mul, one_mul]
  ring

theorem twisted_bound (u : U p) :
    ‖∑ χ ∈ nonprincipal p,(tau χ)^2*χ (u:ZMod p)‖ ≤
      (p.totient:ℝ)*(2*(p:ℝ)^(3/4:ℝ))+1 := by
  have hn : (nonprincipal p) = univ.erase (1 : DirichletCharacter ℂ p) := by ext; simp [nonprincipal]
  have hτ : tau (1:DirichletCharacter ℂ p) = -1 := by
    apply gaussSum_one_left
    intro h
    have he := congrArg (fun ψ : AddChar (ZMod p) ℂ => ψ 1) h
    exact ThetaFourier.char_ne_one (1:ZMod p) one_ne_zero (by simpa using he)
  have hg := sum_erase_add (univ:Finset (DirichletCharacter ℂ p))
    (fun χ => (tau χ)^2*χ (u:ZMod p)) (mem_univ 1)
  rw [second] at hg
  simp only [hτ, neg_one_sq, MulChar.one_apply u.isUnit, one_mul] at hg
  rw [hn, eq_sub_of_add_eq hg]
  apply (norm_sub_le ..).trans
  rw [norm_mul,Complex.norm_natCast,norm_one]
  gcongr
  exact kloosterman_bound _ _ (u⁻¹).ne_zero

#print axioms second
#print axioms twisted_bound
end
end Arxiv.«2501.03234».ThetaGaussAngularKernel
