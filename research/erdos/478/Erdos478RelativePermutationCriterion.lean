import Mathlib.GroupTheory.GroupAction.Jordan
import Mathlib.GroupTheory.Perm.Support

/-! # Full relative permutation action from a prime degree and one transposition -/
namespace Erdos478.RelativeGap
open Equiv MulAction Function

/-- In a transitive prime-degree quotient action, a subgroup element interchanging
exactly two points forces surjectivity onto the entire symmetric group. -/
theorem surjective_of_swap {G X : Type*} [Group G] [Fintype X] [DecidableEq X] (rho : G →* Perm X)
    (prime : (Nat.card X).Prime) (trans : ∀ x y : X, ∃ g, rho g x=y)
    {s : G} (swap : (rho s).IsSwap) : Surjective rho := by
  let H := rho.range
  let _ : IsPretransitive H X := ⟨fun x y => by
    obtain ⟨g,hg⟩ := trans x y
    exact ⟨⟨rho g,g,rfl⟩,hg⟩⟩
  apply MonoidHom.range_eq_top.mp
  exact Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem (IsPreprimitive.of_prime_card prime)
    (rho s) swap ⟨s,rfl⟩

/-- A surjective permutation action on the kernel splits off an independent
permutation coordinate from the lower actions' joint image. -/
theorem range_product {G H P : Type*} [Group G] [Group H] [Group P]
    (lower : G →* H) (next : G →* P) (full : Surjective (next.comp lower.ker.subtype)) :
    Surjective (lower.rangeRestrict.prod next) := by
  rintro ⟨y,t⟩
  obtain ⟨g,hg⟩ := y.prop
  obtain ⟨k,hk⟩ := full (t*(next g)⁻¹)
  refine ⟨k.val*g,Prod.ext (Subtype.ext ?_) ?_⟩
  · change lower (k.val*g)=y.val
    rw [map_mul,show lower k.val=1 from k.prop,one_mul,hg]
  · change next (k.val*g)=t
    rw [map_mul,show next k.val=t*(next g)⁻¹ from hk,inv_mul_cancel_right]

#print axioms surjective_of_swap
#print axioms range_product
end Erdos478.RelativeGap
