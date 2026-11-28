import Erdos722RankClassQuotient
import Mathlib.GroupTheory.Coset.Card

/-! # Vertical checks and full stabilizers on the next-rank stratum -/

namespace Erdos722.QuadSwitch
open Finset Equiv Function MulAction
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}

abbrev SwitchStabilizer (hH : H.IsBlockDesign 3 4) (s : H → Bool) :=
  letI := switchAction hH
  stabilizer (liftGroup H) s

def checkStabilizer (hH : H.IsBlockDesign 3 4) (s : H → Bool) :
    Multiplicative (checkGroup H) →* SwitchStabilizer hH s := by
  letI := switchAction hH
  let F (u : Multiplicative (checkGroup H)) : SwitchStabilizer hH s :=
    ⟨liftCoordinates H (1,flipBit ∘ u.toAdd.val),by
      apply doubling_injective hH
      apply (act_relabels hH _ s).symm.trans
      apply (vertical_iff_check hH s _).mpr
      simp only [comp_def,flipBit_decode]
      exact u.toAdd.prop⟩
  refine { toFun := F, map_one' := ?_, map_mul' := ?_ }
  · apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    rintro ⟨x,b⟩
    change (x,b ^^ flipBit 0)=(x,b)
    rw [show flipBit 0=false by decide,Bool.xor_false]
  · intro u v
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    rintro ⟨x,b⟩
    change (x,b ^^ flipBit (u.toAdd.val x+v.toAdd.val x))=(x,(b ^^ flipBit (v.toAdd.val x)) ^^ flipBit (u.toAdd.val x))
    exact congrArg (Prod.mk x) ((show ∀ (a c : ZMod 2) (i : Bool),
      (i ^^ flipBit (a+c))=((i ^^ flipBit c) ^^ flipBit a) by decide) _ _ _)

theorem checkStabilizer_injective (hH : H.IsBlockDesign 3 4) (s : H → Bool) :
    Injective (checkStabilizer hH s) := by
  intro u v he
  have eq := congrArg (fun z : SwitchStabilizer hH s => z.val.val) he
  have h := (fibrePerm_eq_iff.mp eq).2
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  funext x
  exact (flipBit_decode _).symm.trans ((congrArg bitValue (congrFun h x)).trans (flipBit_decode _))

/-- Off the affine orbit, arbitrary automorphisms descend to the intrinsic
quotient. The stabilizer in the switch action is consequently the full group. -/
def nongaugeStabilizerAut [Nonempty V] (hH : H.IsBlockDesign 3 4) (sep : Separates H) (s : H → Bool)
    (ng : ¬Coboundary s) : SwitchStabilizer hH s ≃* automorphisms (doubling hH s) := by
  letI := switchAction hH
  let f (g : SwitchStabilizer hH s) : automorphisms (doubling hH s) :=
    ⟨g.val.val,(act_relabels hH g.val s).trans (congrArg (doubling hH) g.prop)⟩
  have inj : Injective f := fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : automorphisms (doubling hH s) => z.val) h))
  have sur : Surjective f := by
    intro e
    obtain ⟨σ,u,he⟩ := intrinsic_isomorphism hH sep ng e.val e.prop
    have h : (fibrePerm σ u).finsetCongr.finsetCongr (doubling hH s)=doubling hH s := he ▸ e.prop
    have hm := (maps_doubling_iff hH s s σ u).mp h
    let g : liftGroup H := ⟨e.val,⟨σ,matches_preserves hm⟩,u,he⟩
    have fix : g∈stabilizer (liftGroup H) s :=
      doubling_injective hH ((act_relabels hH g s).symm.trans e.prop)
    exact ⟨⟨g,fix⟩,rfl⟩
  exact { toEquiv := Equiv.ofBijective f ⟨inj,sur⟩, map_mul' := fun _ _ => rfl }

theorem checks_dvd_stabilizer (hH : H.IsBlockDesign 3 4) (s : H → Bool) :
    Nat.card (Checks H)∣Nat.card (SwitchStabilizer hH s) := by
  change Nat.card (Multiplicative (checkGroup H))∣_
  exact Subgroup.card_dvd_of_injective (checkStabilizer hH s) (checkStabilizer_injective hH s)

theorem smallest_stabilizer_group (hH : H.IsBlockDesign 3 4) (s : H → Bool)
    (eq : Nat.card (SwitchStabilizer hH s)=Nat.card (Checks H)) :
    Nonempty (Multiplicative (checkGroup H) ≃* SwitchStabilizer hH s) :=
  ⟨MulEquiv.ofBijective (checkStabilizer hH s) ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨checkStabilizer_injective hH s,eq.symm⟩)⟩

#print axioms SwitchStabilizer
#print axioms checkStabilizer
#print axioms checkStabilizer_injective
#print axioms nongaugeStabilizerAut
#print axioms checks_dvd_stabilizer
#print axioms smallest_stabilizer_group
end
end Erdos722.QuadSwitch
