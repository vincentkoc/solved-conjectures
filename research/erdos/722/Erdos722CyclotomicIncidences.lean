import Erdos722CyclotomicMoment

/-!
# Affine incidence counts

A sample of a set `D` under all affine maps has a computable centered
second moment against any set `S`. The count includes slope zero.
-/

namespace Erdos722.Cyclotomy
open Finset
open scoped Classical
variable {F : Type*} [Field F] [Fintype F]

noncomputable def hits (D S : Finset F) (a b : F) : ℕ :=
  (D.filter fun z => a*z+b ∈ S).card

/-- Exact second moment for incidence counts, with the center multiplied
by the field order to avoid division. -/
theorem incidence_second_moment (D S : Finset F) :
    let q : ℝ := Fintype.card F
    let s : ℝ := S.card
    ∑ t : F × F, (q*hits D S t.1 t.2-(D.card:ℝ)*s)^2 =
      D.card*q^2*s*(q-s) := by
  let q : ℝ := Fintype.card F
  let s : ℝ := S.card
  let f : F → ℝ := fun x => (if x ∈ S then q else 0)-s
  have hf : ∑ x, f x = 0 := by
    simp [f,Finset.sum_sub_distrib,q,s,mul_comm]
  have hsq (x : F) : (f x)^2 = (if x ∈ S then q^2-2*q*s else 0)+s^2 := by
    by_cases h : x ∈ S <;> simp [f,h]
    ring
  have energy : ∑ x, (f x)^2 = q*s*(q-s) := by
    simp_rw [hsq]
    simp [Finset.sum_add_distrib,q,s]
    ring
  have resc (a b : F) : ∑ z ∈ D, f (a*z+b) = q*hits D S a b-D.card*s := by
    simp [f,hits,Finset.sum_sub_distrib,Finset.sum_ite,mul_comm]
  have h := affine_second_moment D f hf
  simp_rw [resc] at h
  rw [energy] at h
  change _ = D.card*q^2*s*(q-s)
  convert h using 1
  dsimp [q,s]
  ring

#print axioms incidence_second_moment

end Erdos722.Cyclotomy
