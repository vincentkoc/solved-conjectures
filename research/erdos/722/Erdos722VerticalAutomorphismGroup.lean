import Erdos722ExceptionalSwitches
import Erdos722BinaryCheckBases

/-! # The full automorphism group of a nonexceptional quadruple double -/

namespace Erdos722.QuadSwitch
open Finset Equiv Function
noncomputable section
variable {V W : Type*}

/-- All point permutations preserving the block family. -/
def automorphisms (H : Finset (Finset V)) : Subgroup (Perm V) where
  carrier := {e | e.finsetCongr.finsetCongr H=H}
  one_mem' := by change (Equiv.refl V).finsetCongr.finsetCongr H=H; simp
  mul_mem' {e f} he hf := by
    change (f.trans e).finsetCongr.finsetCongr H=H
    rw [← Equiv.finsetCongr_trans,← Equiv.finsetCongr_trans,Equiv.trans_apply,hf,he]
  inv_mem' {e} he := by
    exact (congrArg e.finsetCongr.finsetCongr.symm he).symm.trans (e.finsetCongr.finsetCongr.symm_apply_apply H)

def checkGroup (H : Finset (Finset V)) : AddSubgroup (V → ZMod 2) where
  carrier := {u | Check H u}
  zero_mem' := fun B _ => by simp [blockSum]
  add_mem' := fun {u v} hu hv B hb => by
    change (∑ x∈B,(u x+v x))=0
    rw [sum_add_distrib,show (∑ x∈B,u x)=0 from hu B hb,show (∑ x∈B,v x)=0 from hv B hb,add_zero]
  neg_mem' := fun {u} hu B hb => by
    change (∑ x∈B,-u x)=0
    rw [sum_neg_distrib,show (∑ x∈B,u x)=0 from hu B hb,neg_zero]

def automorphismRelabel (e : V ≃ W) (H : Finset (Finset V)) :
    automorphisms H ≃* automorphisms (e.finsetCongr.finsetCongr H) where
  toEquiv := e.permCongr.subtypeEquiv fun σ => by
    change σ.finsetCongr.finsetCongr H=H ↔
      (e.permCongr σ).finsetCongr.finsetCongr (e.finsetCongr.finsetCongr H)=e.finsetCongr.finsetCongr H
    rw [Equiv.permCongr_def,← Equiv.finsetCongr_trans,← Equiv.finsetCongr_trans,
      ← Equiv.finsetCongr_trans,← Equiv.finsetCongr_trans]
    simp only [Equiv.trans_apply,← Equiv.finsetCongr_symm,Equiv.symm_apply_apply,EmbeddingLike.apply_eq_iff_eq]
  map_mul' _ _ := Subtype.ext (e.permCongrHom.map_mul _ _)

def flipBit (z : ZMod 2) : Bool := decide (z=1)

theorem flipBit_decode : ∀ z, bitValue (flipBit z)=z := by decide
theorem flipBit_encode : ∀ b, flipBit (bitValue b)=b := by decide

variable [Fintype V] [DecidableEq V] {H : Finset (Finset V)}

def verticalGroupEquiv (hH : H.IsBlockDesign 3 4) (s : H → Bool) (hs : s∉exceptional hH) :
    Multiplicative (checkGroup H) ≃* automorphisms (doubling hH s) := by
  let F (u : Multiplicative (checkGroup H)) : automorphisms (doubling hH s) :=
    ⟨fibrePerm (Equiv.refl _) (flipBit ∘ u.toAdd.val),(vertical_iff_check hH s _).mpr (by
      simp only [Function.comp_def,flipBit_decode]; exact u.toAdd.prop)⟩
  have inj : Injective F := by
    intro u v eq
    have h := (fibrePerm_eq_iff.mp (congrArg Subtype.val eq)).2
    apply (Multiplicative.toAdd.injective)
    apply Subtype.ext
    funext x
    exact (flipBit_decode _).symm.trans ((congrArg bitValue (congrFun h x)).trans (flipBit_decode _))
  have sur : Surjective F := by
    intro e
    obtain ⟨f,hf,check⟩ := (nonexceptional_automorphisms hH s hs e.val).mp e.prop
    refine ⟨Multiplicative.ofAdd (⟨bitValue ∘ f,check⟩ : checkGroup H),Subtype.ext ?_⟩
    rw [hf]
    exact fibrePerm_eq_iff.mpr ⟨rfl,funext fun x => flipBit_encode (f x)⟩
  refine { toEquiv := Equiv.ofBijective F ⟨inj,sur⟩, map_mul' := ?_ }
  intro u v
  apply Subtype.ext
  apply Equiv.ext
  rintro ⟨x,b⟩
  change (x,b ^^ flipBit (u.toAdd.val x+v.toAdd.val x))=(x,(b ^^ flipBit (v.toAdd.val x)) ^^ flipBit (u.toAdd.val x))
  exact congrArg (Prod.mk x) ((show ∀ (b : Bool) (z w : ZMod 2), (b ^^ flipBit (z+w))=((b ^^ flipBit w) ^^ flipBit z) by decide) b _ _)

theorem vertical_group_order (hH : H.IsBlockDesign 3 4) (s : H → Bool) (hs : s∉exceptional hH) :
    Nat.card (automorphisms (doubling hH s))=Nat.card (Checks H) :=
  (Nat.card_congr (verticalGroupEquiv hH s hs).toEquiv).symm

#print axioms automorphisms
#print axioms checkGroup
#print axioms automorphismRelabel
#print axioms flipBit
#print axioms flipBit_decode
#print axioms flipBit_encode
#print axioms verticalGroupEquiv
#print axioms vertical_group_order
end
end Erdos722.QuadSwitch
