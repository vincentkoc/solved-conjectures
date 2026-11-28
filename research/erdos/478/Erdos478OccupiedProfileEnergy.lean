import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! # Ordered fibre collisions and the number of realised profiles -/

namespace Erdos478.CyclotomicProfiles
open Finset
open scoped Classical
noncomputable section
variable {X Y : Type*}

def equalPairs [DecidableEq Y] (A : Finset X) (f : X → Y) := (A ×ˢ A).filter (fun xy => f xy.1=f xy.2)

/-- A map taking few values must identify many ordered pairs of arguments. -/
theorem support_energy [DecidableEq Y] (A : Finset X) (f : X → Y) :
    A.card^2 ≤ (A.image f).card*(equalPairs A f).card := by
  let S := A.image f
  let fibres (y : Y) := A.filter fun x => f x=y
  have mass := card_eq_sum_card_fiberwise (s:=A) (t:=S) (f:=f) (fun x hx => mem_image_of_mem _ hx)
  let E := equalPairs A f
  have sum := card_eq_sum_card_fiberwise (s:=E) (t:=S) (f:=fun xy => f xy.1) (fun xy h =>
    mem_image_of_mem _ (mem_product.mp (mem_filter.mp h).1).1)
  have each (y : Y) : E.filter (fun xy => f xy.1=y)=(fibres y) ×ˢ (fibres y) := by
    ext ⟨x,z⟩
    simp only [E,equalPairs,mem_filter,mem_product,fibres]
    grind
  simp only [each,card_product,← sq] at sum
  have cs := sum_mul_sq_le_sq_mul_sq (R:=ℕ) S (fun _ => 1) (fun y => (fibres y).card)
  simp only [one_mul,one_pow,sum_const,smul_eq_mul,mul_one] at cs
  change (∑ y∈S,(fibres y).card)^2 ≤ S.card*∑ y∈S,(fibres y).card^2 at cs
  rw [← sum] at cs
  exact mass ▸ cs

#print axioms equalPairs
#print axioms support_energy
end
end Erdos478.CyclotomicProfiles
