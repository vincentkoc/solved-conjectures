import ThetaGaussAngularKernel

/-! Multiplying a character test by a finite linear combination of twists. -/

namespace Arxiv.«2501.03234».ThetaAngularTests
open Finset Complex DirichletCharacter ThetaPointwiseCutoff ThetaHalfSpectrum ThetaGaussAngularKernel
open ThetaCharacterFourthMoment (U transform)
open scoped ComplexConjugate
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def TwistedBound (W : DirichletCharacter ℂ p → ℂ) (D : ℝ) : Prop :=
  ∀ u : U p, ‖∑ χ ∈ nonprincipal p, W χ * χ (u:ZMod p)‖ ≤ D

def lin (f : U p → ℂ) (σ : U p → U p) (χ : DirichletCharacter ℂ p) : ℂ :=
  ∑ x : U p, f x * χ (↑(σ x):ZMod p)

theorem multiply {W : DirichletCharacter ℂ p → ℂ} {D : ℝ} (h : TwistedBound W D)
    (f : U p → ℂ) (σ : U p → U p) :
    TwistedBound (fun χ => W χ * lin f σ χ) (D * ∑ x, ‖f x‖) := by
  intro u
  have e : (∑ χ ∈ nonprincipal p, W χ * lin f σ χ * χ (u:ZMod p)) =
      ∑ x : U p, f x * ∑ χ ∈ nonprincipal p, W χ * χ (↑(σ x*u):ZMod p) := by
    simp only [lin,mul_sum,sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro χ _
    simp [mul_left_comm,mul_comm]
  rw [e,mul_sum]
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro x _
  rw [norm_mul,mul_comm D]
  exact mul_le_mul_of_nonneg_left (h _) (norm_nonneg _)

def F (χ : DirichletCharacter ℂ p) : ℂ := transform freq χ⁻¹

def variation (p : ℕ) [Fact p.Prime] : ℝ := ∑ x : U p, ‖freq x‖

private lemma mul_F {W : DirichletCharacter ℂ p → ℂ} {D : ℝ} (h : TwistedBound W D) :
    TwistedBound (fun χ => W χ*F χ) (D*variation p) := by
  simpa only [F,transform,lin,MulChar.inv_apply',Units.val_inv_eq_inv_val,variation] using
    multiply h freq (fun x => x⁻¹)

private lemma mul_conjF {W : DirichletCharacter ℂ p → ℂ} {D : ℝ} (h : TwistedBound W D) :
    TwistedBound (fun χ => W χ*conj (F χ)) (D*variation p) := by
  have he (χ : DirichletCharacter ℂ p) :
      conj (F χ) = lin (fun x => conj (freq x)) id χ := by
    simp only [F,transform,lin,map_sum,map_mul,id_eq]
    apply sum_congr rfl
    intro x _
    congr 1
    exact (MulChar.star_apply' χ⁻¹ (x:ZMod p)).trans (by simp)
  simpa only [he,Complex.norm_conj,variation] using multiply h (fun x => conj (freq x)) id

theorem product_tests {W : DirichletCharacter ℂ p → ℂ} {D : ℝ} (h : TwistedBound W D) (a b : ℕ) :
    TwistedBound (fun χ => W χ*(F χ)^a*(conj (F χ))^b) (D*(variation p)^(a+b)) := by
  have ha (k : ℕ) : TwistedBound (fun χ => W χ*(F χ)^k) (D*(variation p)^k) := by
    induction k with
    | zero => simpa using h
    | succ k ih => simpa only [pow_succ,mul_assoc] using mul_F ih
  induction b with
  | zero => simpa using ha a
  | succ b ih =>
    simpa only [Nat.add_succ,pow_succ,mul_assoc] using mul_conjF ih

#print axioms product_tests
end
end Arxiv.«2501.03234».ThetaAngularTests
