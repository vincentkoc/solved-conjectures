import ThetaSignedCubicMass

/-! A finite fourth-moment bound for multiplicative character transforms. -/
namespace Arxiv.«2501.03234».ThetaCharacterFourthMoment
open Finset Complex DirichletCharacter
open scoped ComplexConjugate
noncomputable section
variable {G : Type*} [CommGroup G] [Fintype G]

def convolution (f : G → ℂ) (y : G) : ℂ := ∑ x,f x*f (y/x)

/-- Young's 4/3,4/3,2 convolution bound in a form requiring only integer powers. -/
theorem convolution_bound (f : G → ℂ) (u : G → ℝ) (hu : ∀ x,0≤u x)
    (hf : ∀ x,‖f x‖≤(u x)^3) :
    ∑ y,‖convolution f y‖^2 ≤ (∑ x,(u x)^4)^3 := by
  classical
  let H := ∑ x,(u x)^4
  have hH : 0≤H := sum_nonneg (fun x _ => by positivity)
  have shift (y : G) : ∑ x,(u (y/x))^4 = H := (Equiv.divLeft y).sum_comp (fun x => (u x)^4)
  have one (y : G) : ‖convolution f y‖^2 ≤ H*∑ x,(u x)^4*(u (y/x))^4 := by
    have hc := sum_mul_sq_le_sq_mul_sq univ (fun x => (u x)^2) (fun x => (u (y/x))^2)
    simp only [←pow_mul,Nat.reduceMul,shift] at hc
    have hb : (∑ x,(u x)^2*(u (y/x))^2)≤H := by nlinarith only [hc,hH]
    have hd := sum_mul_sq_le_sq_mul_sq univ (fun x => (u x)^2*(u (y/x))^2)
      (fun x => u x*u (y/x))
    simp only [mul_pow,←pow_mul,Nat.reduceMul] at hd
    have hnorm : ‖convolution f y‖≤∑ x,(u x)^2*(u (y/x))^2*(u x*u (y/x)) := by
      refine (norm_sum_le ..).trans (sum_le_sum (fun x _ => ?_))
      rw [norm_mul]
      exact (mul_le_mul (hf x) (hf (y/x)) (norm_nonneg _) (pow_nonneg (hu x) _)).trans_eq (by ring)
    exact ((pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hd).trans
      ((mul_le_mul_of_nonneg_left hb (sum_nonneg (fun x _ => mul_nonneg (by positivity) (by positivity)))).trans_eq (mul_comm ..))
  apply (sum_le_sum (fun y _ => one y)).trans_eq
  rw [←mul_sum,sum_comm]
  simp_rw [←mul_sum,show ∀ x : G,(∑ y,(u (y/x))^4)=H from
    fun x => (Equiv.divRight x).sum_comp (fun y => (u y)^4),←sum_mul]
  change H*(H*H)=H^3; ring

variable {p : ℕ} [Fact p.Prime]
abbrev U (p : ℕ) := (ZMod p)ˣ

def transform (f : U p → ℂ) (χ : DirichletCharacter ℂ p) := ∑ x,f x*χ (x:ZMod p)

theorem product (f : U p → ℂ) (χ : DirichletCharacter ℂ p) :
    (transform f χ)^2 = transform (convolution f) χ := by
  classical
  unfold transform convolution
  rw [pow_two]; simp only [sum_mul,mul_sum]
  rw [sum_comm (s:=univ) (t:=univ) (f:=fun y x : U p => f x*f (y/x)*χ (y:ZMod p))]
  apply sum_congr rfl; intro x _
  apply Fintype.sum_equiv (Equiv.mulLeft x) _ _
  intro y; simp [mul_assoc,mul_comm,mul_left_comm]

theorem parseval (f : U p → ℂ) :
    ∑ χ : DirichletCharacter ℂ p,‖transform f χ‖^2 =
      (p.totient:ℝ)*∑ x,‖f x‖^2 := by
  classical
  have h (x y : U p) : (∑ χ : DirichletCharacter ℂ p,χ (x:ZMod p)*conj (χ (y:ZMod p))) =
      if y=x then (p.totient:ℂ) else 0 := by
    simp_rw [show ∀ χ : DirichletCharacter ℂ p,conj (χ (y:ZMod p))=χ⁻¹ (y:ZMod p) from
      fun χ => MulChar.star_apply' χ _]
    simpa only [MulChar.inv_apply',mul_comm,Units.val_inj] using
      (sum_char_inv_mul_char_eq (R:=ℂ) y.isUnit (x:ZMod p))
  have norm2 (z : ℂ) : ((‖z‖^2:ℝ):ℂ) = z*conj z := by rw [mul_conj,normSq_eq_norm_sq]
  apply Complex.ofReal_injective
  push_cast only [ofReal_sum,ofReal_mul]
  simp_rw [norm2]
  unfold transform
  simp only [map_sum,map_mul,sum_mul,mul_sum]
  simp_rw [sum_comm (s:=(univ : Finset (DirichletCharacter ℂ p))) (t:=(univ : Finset (U p)))]
  have fac (x y : U p) (χ : DirichletCharacter ℂ p) :
      f x*χ (x:ZMod p)*(conj (f y)*conj (χ (y:ZMod p))) =
        (f x*conj (f y))*(χ (x:ZMod p)*conj (χ (y:ZMod p))) := by ring
  simp_rw [fac,←mul_sum,h]
  simp [mul_ite,mul_sum,mul_comm,mul_left_comm]

theorem fourth (f : U p → ℂ) (u : U p → ℝ) (hu : ∀ x,0≤u x) (hf : ∀ x,‖f x‖≤(u x)^3) :
    ∑ χ : DirichletCharacter ℂ p,‖transform f χ‖^4 ≤ (p.totient:ℝ)*(∑ x,(u x)^4)^3 := by
  have H := parseval (convolution f)
  have h (χ : DirichletCharacter ℂ p) : ‖transform f χ‖^4=‖transform (convolution f) χ‖^2 := by
    rw [←product,norm_pow,←pow_mul]
  simp_rw [h,H]
  exact mul_le_mul_of_nonneg_left (convolution_bound f u hu hf) (Nat.cast_nonneg _)

#print axioms fourth
end
end Arxiv.«2501.03234».ThetaCharacterFourthMoment
