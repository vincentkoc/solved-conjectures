import Erdos722VerticalAutomorphismGroup
import Mathlib.GroupTheory.GroupAction.Quotient

/-! # The finite group acting on all block switches of a fixed quadruple system -/

namespace Erdos722.QuadSwitch
open Finset Equiv Function
noncomputable section
variable {V : Type*} {H : Finset (Finset V)}

def liftGroup (H : Finset (Finset V)) : Subgroup (Perm (V × Bool)) where
  carrier := {e | ∃ (σ : automorphisms H) (f : V → Bool), e=fibrePerm σ.val f}
  one_mem' := ⟨1,fun _ => false,Equiv.ext fun ⟨x,b⟩ => by cases b <;> rfl⟩
  mul_mem' := by
    rintro _ _ ⟨σ,f,rfl⟩ ⟨τ,g,rfl⟩
    refine ⟨σ*τ,fun x => g x ^^ f (τ.val x),Equiv.ext fun ⟨x,b⟩ => ?_⟩
    change (_, (b ^^ g x) ^^ f (τ.val x))=(_, b ^^ (g x ^^ f (τ.val x)))
    rw [Bool.xor_assoc]
    rfl
  inv_mem' := by
    rintro _ ⟨σ,f,rfl⟩
    exact ⟨σ⁻¹,f ∘ σ.val.symm,Equiv.ext fun _ => rfl⟩

def liftCoordinates (H : Finset (Finset V)) : automorphisms H × (V → Bool) ≃ liftGroup H := by
  let F (p : automorphisms H × (V → Bool)) : liftGroup H := ⟨fibrePerm p.1.val p.2,p.1,p.2,rfl⟩
  apply Equiv.ofBijective F
  constructor
  · intro a b eq
    have ⟨e,f⟩ := fibrePerm_eq_iff.mp (congrArg Subtype.val eq)
    exact Prod.ext (Subtype.ext e) f
  · rintro ⟨e,σ,f,rfl⟩
    exact ⟨(σ,f),rfl⟩

theorem liftCoordinates_val (p : automorphisms H × (V → Bool)) :
    (liftCoordinates H p).val=fibrePerm p.1.val p.2 := rfl

def switchTransport (σ : automorphisms H) (f : V → Bool) (s : H → Bool) (j : H) : Bool :=
  let i := (blockPerm σ.val σ.prop).symm j
  flipBit (blockSum (bitValue ∘ f) i.val+bitValue (s i))

theorem transport_matches (σ : automorphisms H) (f : V → Bool) (s : H → Bool) :
    Matches s (switchTransport σ f s) σ.val f := by
  apply (matches_iff_equations _ _ _ _ σ.prop).mpr
  intro i
  simp only [switchTransport,Equiv.symm_apply_apply,flipBit_decode]

def actOnSwitch (g : liftGroup H) (s : H → Bool) : H → Bool :=
  let p := (liftCoordinates H).symm g
  switchTransport p.1 p.2 s

variable [Fintype V] [DecidableEq V]

theorem act_relabels (hH : H.IsBlockDesign 3 4) (g : liftGroup H) (s : H → Bool) :
    g.val.finsetCongr.finsetCongr (doubling hH s)=doubling hH (actOnSwitch g s) := by
  obtain ⟨⟨σ,f⟩,rfl⟩ := (liftCoordinates H).surjective g
  simp only [actOnSwitch,Equiv.symm_apply_apply,liftCoordinates_val]
  exact (maps_doubling_iff ..).mpr (transport_matches σ f s)

@[instance_reducible] def switchAction (hH : H.IsBlockDesign 3 4) : MulAction (liftGroup H) (H → Bool) where
  smul := actOnSwitch
  one_smul s := doubling_injective hH ((act_relabels hH 1 s).symm.trans (by
    change (Equiv.refl _).finsetCongr.finsetCongr _=_
    simp))
  mul_smul g k s := by
    apply doubling_injective hH
    change doubling hH (actOnSwitch (g*k) s)=doubling hH (actOnSwitch g (actOnSwitch k s))
    rw [← act_relabels,← act_relabels,← act_relabels]
    change (k.val.trans g.val).finsetCongr.finsetCongr _=_
    rw [← Equiv.finsetCongr_trans,← Equiv.finsetCongr_trans,Equiv.trans_apply]

def designIsoSetoid (W : Type*) : Setoid (Finset (Finset W)) where
  r := Isomorphic
  iseqv := {
    refl := fun D => ⟨Equiv.refl _,by simp⟩
    symm := by
      rintro D E ⟨e,he⟩
      exact ⟨e.symm,he ▸ e.finsetCongr.finsetCongr.symm_apply_apply D⟩
    trans := by
      rintro D E A ⟨e,he⟩ ⟨f,hf⟩
      exact ⟨e.trans f,by rw [← Equiv.finsetCongr_trans,← Equiv.finsetCongr_trans,Equiv.trans_apply,he,hf]⟩ }

private theorem reverse_iso {W : Type*} {A B : Finset (Finset W)} (h : Isomorphic A B) : Isomorphic B A :=
  (designIsoSetoid W).iseqv.symm (x:=A) (y:=B) h

/-- Quotient by unrestricted isomorphism of the resulting doubles. -/
def SwitchClasses (hH : H.IsBlockDesign 3 4) := Quotient ((designIsoSetoid (V × Bool)).comap (doubling hH))

theorem class_orbits [Nonempty V] (hH : H.IsBlockDesign 3 4) (sep : Separates H) :
    letI := switchAction hH
    Nat.card (SwitchClasses hH)=Nat.card (Quotient (MulAction.orbitRel (liftGroup H) (H → Bool))) := by
  let _ := switchAction hH
  apply Nat.card_congr
  apply Quotient.congr (Equiv.refl _)
  intro s t
  change Isomorphic (doubling hH s) (doubling hH t) ↔ ∃ g : liftGroup H, actOnSwitch g t=s
  constructor
  · intro iso
    have inv := reverse_iso iso
    obtain ⟨σ,f,h⟩ := (isomorphic_iff_matches hH sep t s).mp inv
    let g := liftCoordinates H (⟨σ,matches_preserves h⟩,f)
    exact ⟨g,doubling_injective hH ((act_relabels hH g t).symm.trans ((maps_doubling_iff ..).mpr h))⟩
  · rintro ⟨g,rfl⟩
    exact reverse_iso ⟨g.val,act_relabels hH g t⟩

#print axioms liftGroup
#print axioms liftCoordinates
#print axioms liftCoordinates_val
#print axioms switchTransport
#print axioms transport_matches
#print axioms actOnSwitch
#print axioms act_relabels
#print axioms switchAction
#print axioms designIsoSetoid
#print axioms SwitchClasses
#print axioms class_orbits
end
end Erdos722.QuadSwitch
