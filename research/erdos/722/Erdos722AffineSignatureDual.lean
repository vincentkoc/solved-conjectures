import Erdos722AffineCheckModel
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.Finiteness

/-! # Binary checks are exactly the affine functions on the signature image -/

namespace Erdos722.QuadSwitch
open Finset Function Module
noncomputable section
variable {V : Type*} [DecidableEq V] {H : Finset (Finset V)}

abbrev labelSpace (hH : H.IsBlockDesign 3 4) (a : V) :=
  AddSubgroup.toZModSubmodule 2 (signatureSpace hH a)

def label (hH : H.IsBlockDesign 3 4) (a x : V) : labelSpace hH a :=
  ⟨signature H x+signature H a,x,rfl⟩

theorem label_surjective (hH : H.IsBlockDesign 3 4) (a : V) : Surjective (label hH a) := by
  rintro ⟨_,x,hx⟩
  exact ⟨x,Subtype.ext hx⟩

@[simp] theorem label_origin (hH : H.IsBlockDesign 3 4) (a : V) : label hH a a=0 := by
  apply Subtype.ext
  funext f
  exact CharTwo.add_self_eq_zero _

theorem label_block_sum (hH : H.IsBlockDesign 3 4) (a : V) {B : Finset V} (hb : B∈H) :
    ∑ x∈B,label hH a x=0 := by
  apply Subtype.ext
  change (labelSpace hH a).subtype (∑ x∈B,label hH a x)=0
  rw [map_sum]
  change ∑ x∈B,(signature H x+signature H a)=0
  rw [sum_add_distrib,signature_sum hb,sum_const,hH.1 B hb,zero_add]
  funext f
  change 4 • (signature H a f)=0
  rw [nsmul_eq_mul]
  norm_num
  exact Or.inl (by decide)

def affineCheck (hH : H.IsBlockDesign 3 4) (a : V)
    (v : (Module.Dual (ZMod 2) (labelSpace hH a)) × ZMod 2) : Checks H :=
  ⟨fun x => v.1 (label hH a x)+v.2,by
    intro B hb
    rw [blockSum,sum_add_distrib,← map_sum,label_block_sum hH a hb,map_zero,zero_add,sum_const,hH.1 B hb]
    rw [nsmul_eq_mul]
    norm_num
    exact Or.inl (by decide)⟩

/-- Each check has a unique constant and linear part. Point signatures may have
arbitrary multiplicity and this equivalence still holds. -/
def affineChecksEquiv (hH : H.IsBlockDesign 3 4) (a : V) :
    ((Module.Dual (ZMod 2) (labelSpace hH a)) × ZMod 2) ≃ Checks H := by
  apply Equiv.ofBijective (affineCheck hH a)
  constructor
  · rintro ⟨L,c⟩ ⟨M,d⟩ eq
    have same (x : V) := congrArg (fun u : Checks H => u.val x) eq
    change ∀ x, L (label hH a x)+c=M (label hH a x)+d at same
    have cd : c=d := by simpa using same a
    subst d
    congr 1
    apply LinearMap.ext
    intro z
    obtain ⟨x,rfl⟩ := label_surjective hH a z
    exact add_right_cancel (same x)
  · intro u
    let L : Module.Dual (ZMod 2) (labelSpace hH a) :=
      { toFun := fun z => z.val u, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    refine ⟨⟨L,u.val a⟩,Subtype.ext (funext fun x => ?_)⟩
    change (u.val x+u.val a)+u.val a=u.val x
    rw [add_assoc,CharTwo.add_self_eq_zero,add_zero]

theorem label_card_checks [Finite V] (hH : H.IsBlockDesign 3 4) (a : V) :
    Nat.card (Checks H)=2*Nat.card (labelSpace hH a) := by
  classical
  rw [← Nat.card_congr (affineChecksEquiv hH a),Nat.card_prod,
    Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Module.Dual (ZMod 2) (labelSpace hH a)),
    Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=labelSpace hH a),
    Subspace.dual_finrank_eq]
  simp [Nat.card_eq_fintype_card,mul_comm]

#print axioms labelSpace
#print axioms label
#print axioms label_surjective
#print axioms label_origin
#print axioms label_block_sum
#print axioms affineCheck
#print axioms affineChecksEquiv
#print axioms label_card_checks
end
end Erdos722.QuadSwitch
