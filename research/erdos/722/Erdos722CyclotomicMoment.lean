import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Second moments of affine samples in a finite field

For two distinct inputs, slope and intercept run through every pair of
output values exactly once. Including slope zero makes the covariance
vanish exactly for any function with sum zero.
-/

namespace Erdos722.Cyclotomy
open Finset
open scoped Classical
variable {F : Type*} [Field F] [Fintype F]

private def affinePair {z w : F} (hne : z ≠ w) : F × F ≃ F × F where
  toFun t := (t.1*z+t.2,t.1*w+t.2)
  invFun p := ((p.1-p.2)/(z-w),p.1-((p.1-p.2)/(z-w))*z)
  left_inv := by
    rintro ⟨a,b⟩
    have h : (a*z+b-(a*w+b))/(z-w) = a :=
      (div_eq_iff (sub_ne_zero.mpr hne)).2 (by ring)
    dsimp only
    rw [h]
    congr 1
    ring
  right_inv := by
    rintro ⟨u,v⟩
    apply Prod.ext <;> dsimp
    · ring
    · field_simp [sub_ne_zero.mpr hne]
      ring

private theorem affine_sum (f : F → ℝ) (z : F) :
    ∑ t : F × F, f (t.1*z+t.2) = (Fintype.card F : ℝ)*∑ u, f u := by
  rw [Fintype.sum_prod_type]
  have h (a : F) : ∑ b, f (a*z+b) = ∑ u, f u :=
    Equiv.sum_comp (Equiv.addLeft (a*z)) f
  simp_rw [h]
  simp

private theorem affine_cross (f : F → ℝ) (hf : ∑ x, f x = 0)
    {z w : F} (hne : z ≠ w) :
    ∑ t : F × F, f (t.1*z+t.2)*f (t.1*w+t.2) = 0 := by
  calc
    _ = ∑ t : F × F, f t.1*f t.2 :=
      Equiv.sum_comp (affinePair hne) (fun t => f t.1*f t.2)
    _ = _ := by simp [Fintype.sum_prod_type,← Finset.mul_sum,hf]

/-- Summing the squared centered affine sample over all slopes and shifts
leaves just the diagonal terms. -/
theorem affine_second_moment (D : Finset F) (f : F → ℝ) (hf : ∑ x, f x = 0) :
    ∑ t : F × F, (∑ z ∈ D, f (t.1*z+t.2))^2 =
      (D.card : ℝ)*Fintype.card F*∑ u, (f u)^2 := by
  have hcross (z w : F) :
      ∑ t : F × F, f (t.1*z+t.2)*f (t.1*w+t.2) =
        if z=w then (Fintype.card F : ℝ)*∑ u, (f u)^2 else 0 := by
    split_ifs with e
    · subst w
      simp only [← sq]
      exact affine_sum (fun u => (f u)^2) z
    · exact affine_cross f hf e
  calc
    _ = ∑ z ∈ D, ∑ w ∈ D, ∑ t : F × F, f (t.1*z+t.2)*f (t.1*w+t.2) := by
      simp only [sq,Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro z _
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro w _
      exact sum_congr rfl (fun _ _ => mul_comm ..)
    _ = _ := by simp [hcross,mul_assoc]

#print axioms affine_second_moment

end Erdos722.Cyclotomy
