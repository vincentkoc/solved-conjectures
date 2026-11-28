import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Tactic

/-! # Order of the affine permutation group of a prime field -/

namespace Erdos478.PrimeDifferences
open Equiv
noncomputable section
variable (p : ℕ) [Fact p.Prime]

def affineSubgroup : Subgroup (Perm (ZMod p)) where
  carrier := {g | ∃ a : (ZMod p)ˣ, ∃ b, ∀ x, g x=a*x+b}
  one_mem' := ⟨1,0,by simp⟩
  mul_mem' := by
    rintro g h ⟨a,b,hg⟩ ⟨c,d,hh⟩
    exact ⟨a*c,a*d+b,fun x => by simp only [Perm.mul_apply,hg,hh,Units.val_mul]; ring⟩
  inv_mem' := by
    rintro g ⟨a,b,hg⟩
    refine ⟨a⁻¹,-((a⁻¹ : (ZMod p)ˣ) : ZMod p)*b,fun x => ?_⟩
    apply g.injective
    change g (g.symm x)=g _
    rw [g.apply_symm_apply,hg]
    simp only [mul_add,← mul_assoc,mul_neg,Units.mul_inv,one_mul,neg_mul,neg_add_cancel_right]

private def affinePerm (a : (ZMod p)ˣ) (b : ZMod p) : Perm (ZMod p) :=
  (Equiv.mulLeft₀ (a : ZMod p) a.ne_zero).trans (Equiv.addRight b)

private theorem affineEquiv : Nonempty (((ZMod p)ˣ × ZMod p) ≃ affineSubgroup p) := by
  let f (ab : (ZMod p)ˣ × ZMod p) : affineSubgroup p :=
    ⟨affinePerm p ab.1 ab.2,ab.1,ab.2,fun _ => rfl⟩
  refine ⟨Equiv.ofBijective f ⟨?_,?_⟩⟩
  · rintro ⟨a,b⟩ ⟨c,d⟩ h
    have he (x : ZMod p) : (a:ZMod p)*x+b=(c:ZMod p)*x+d :=
      congrArg (fun g : affineSubgroup p => g.val x) h
    have hb : b=d := by simpa using he 0
    have ha : (a:ZMod p)=(c:ZMod p) := add_right_cancel (by simpa [hb] using he 1 : (a:ZMod p)+d=(c:ZMod p)+d)
    exact Prod.ext (Units.ext ha) hb
  · rintro ⟨g,a,b,hg⟩
    exact ⟨(a,b),Subtype.ext (Equiv.ext (fun x => (hg x).symm))⟩

theorem affineSubgroup_card : Nat.card (affineSubgroup p)=p*(p-1) := by
  rw [← Nat.card_congr (affineEquiv p).some,Nat.card_prod,Nat.card_units,Nat.card_eq_fintype_card,ZMod.card,mul_comm]

variable {p} {G : Type*} [Group G]

theorem card_dvd_of_affine (ρ : G →* Perm (ZMod p)) (hinj : Function.Injective ρ)
    (ha : ∀ g, ∃ a b : ZMod p, ∀ x, ρ g x=a*x+b) : Nat.card G∣p*(p-1) := by
  have hm (g : G) : ρ g∈affineSubgroup p := by
    obtain ⟨a,b,h⟩ := ha g
    have han : a≠0 := by
      intro hz
      have := (ρ g).injective (show ρ g 0=ρ g 1 by simp [h,hz])
      exact zero_ne_one this
    exact ⟨Units.mk0 a han,b,h⟩
  let i := ρ.codRestrict (affineSubgroup p) hm
  rw [← affineSubgroup_card]
  exact Subgroup.card_dvd_of_injective i (fun _ _ he => hinj (congrArg Subtype.val he))

#print axioms affineSubgroup_card
#print axioms card_dvd_of_affine
end
end Erdos478.PrimeDifferences
