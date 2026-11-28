import Erdos478FixedPointAverages
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FieldSimp

/-! # Uniform probabilities under a surjective finite group homomorphism -/

namespace Erdos478.LowGapAction
open Finset FrobeniusCounts
noncomputable section
variable {G H : Type*} [Group G] [Group H]

/-- All fibres have the same size. The first coordinate is the given homomorphism. -/
def groupFibres (f : G →* H) (hf : Function.Surjective f) : G ≃ H × f.ker :=
  let s (y : H) := (hf y).choose
  let hs (y : H) : f (s y)=y := (hf y).choose_spec
  { toFun := fun x => ⟨f x,⟨(s (f x))⁻¹*x,by simp [MonoidHom.mem_ker,hs]⟩⟩
    invFun := fun q => s q.1*q.2.val
    left_inv := fun x => mul_inv_cancel_left _ _
    right_inv := by
      rintro ⟨y,k⟩
      have eq : f (s y*k.val)=y := by rw [map_mul,hs,show f k.val=1 from k.prop,mul_one]
      exact Prod.ext eq (Subtype.ext (by dsimp only; rw [eq,inv_mul_cancel_left])) }

theorem quotient_mean [Fintype G] [Fintype H] (f : G →* H) (hf : Function.Surjective f) (w : H → ℝ) :
    uniform G (fun g => w (f g))=uniform H w := by
  classical
  let F := groupFibres f hf
  have sums : (∑ g,w (f g))=∑ q : H × f.ker,w q.1 :=
    F.sum_comp (fun q : H × f.ker => w q.1)
  have size := Fintype.card_congr F
  rw [Fintype.card_prod] at size
  change (∑ g,w (f g))/Fintype.card G=(∑ y,w y)/Fintype.card H
  rw [sums,Fintype.sum_prod_type,size]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Finset.mul_sum,Nat.cast_mul]
  have nz : (Fintype.card f.ker : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp [nz]

#print axioms groupFibres
#print axioms quotient_mean
end
end Erdos478.LowGapAction
