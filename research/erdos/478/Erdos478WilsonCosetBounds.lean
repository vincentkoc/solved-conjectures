import Erdos478WilsonQuotientReflection

/-! # Wilson-separated cosets of a subgroup containing minus one -/

namespace Erdos478.QuotientSpacing
open Finset ReturnConcentration
open scoped Classical
noncomputable section

theorem coset_avoids_products (p : ℕ) [Fact p.Prime] (H : Subgroup (ZMod p)ˣ) (g : (ZMod p)ˣ)
    (sign : -1∈H) (outside : g^2∉H) {x y : ZMod p}
    (hx : x∈unitCoset p H g) (hy : y∈unitCoset p H g) : x*y≠1 ∧ x*y≠-1 := by
  obtain ⟨v,_,rfl⟩ := mem_image.mp hx
  obtain ⟨w,_,rfl⟩ := mem_image.mp hy
  have avoid (u : (ZMod p)ˣ) (hu : u∈H) : (g*v.val)*(g*w.val)≠u := by
    intro eq
    apply outside
    have ident : g^2=u*(v.val*w.val)⁻¹ := by
      have prod : u=g^2*(v.val*w.val) := by rw [← eq,pow_two]; ac_rfl
      rw [prod,mul_inv_cancel_right]
    rw [ident]
    exact H.mul_mem hu (H.inv_mem (H.mul_mem v.prop w.prop))
  exact ⟨fun h => avoid 1 H.one_mem (Units.ext h),fun h => avoid (-1) sign (Units.ext h)⟩

theorem reflected_coset_bound (p : ℕ) [hp : Fact p.Prime] (a b : ℕ) (ha : 1≤a) (hb : b<p)
    (H : Subgroup (ZMod p)ˣ) (g : (ZMod p)ˣ) (sign : -1∈H) (outside : g^2∉H) :
    16*((hits p a b (unitCoset p H g)).card-1)^3 ≤ 9*Nat.card H*(b-a)^2 := by
  let S := unitCoset p H g
  let A := hits p a b S
  let D := quotientSet S
  have sub : A ⊆ Icc a b := filter_subset ..
  have fits : A ⊆ Ico 1 p := fun i hi =>
    mem_Ico.mpr ⟨ha.trans (mem_Icc.mp (sub hi)).1,lt_of_le_of_lt (mem_Icc.mp (sub hi)).2 hb⟩
  have sep : avoidsWilson p A := fun _ hi _ hj =>
    coset_avoids_products p H g sign outside (mem_filter.mp hi).2 (mem_filter.mp hj).2
  have neg : ∀ u∈D,-u∈D := by
    intro u hu
    rw [show D= _ from coset_quotient_set p H g] at hu ⊢
    obtain ⟨v,_,rfl⟩ := mem_image.mp hu
    exact mem_image.mpr ⟨⟨(-1)*v.val,H.mul_mem sign v.prop⟩,mem_univ _,by simp⟩
  have bound := reflected_bound hp.out A fits sep D (target_quotients S) neg
  have inj : Function.Injective (fun x : H => (x.val:ZMod p)) := Units.val_injective.comp Subtype.val_injective
  rw [show D= _ from coset_quotient_set p H g,card_image_of_injective _ inj,card_univ,← Nat.card_eq_fintype_card] at bound
  exact bound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (width_le sub) 2))

#print axioms coset_avoids_products
#print axioms reflected_coset_bound
end
end Erdos478.QuotientSpacing
