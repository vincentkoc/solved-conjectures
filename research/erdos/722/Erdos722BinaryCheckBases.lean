import Erdos722SwitchIsomorphismLaw
import Erdos722PointedDesignProduct

/-! # Separating binary quadruple systems from iterated zero switches -/

namespace Erdos722.QuadSwitch
open Finset Equiv Function
noncomputable section

abbrev Checks {V : Type*} (H : Finset (Finset V)) := {u : V → ZMod 2 // Check H u}

def checkRelabel {V W : Type*} (e : V ≃ W) (H : Finset (Finset V)) :
    Checks (e.finsetCongr.finsetCongr H) ≃ Checks H :=
  (e.symm.arrowCongr (Equiv.refl _)).subtypeEquiv fun f => check_relabel e H f

theorem relabel_quadruples {V W : Type*} [DecidableEq W] (e : V ≃ W) {H : Finset (Finset V)}
    (hH : H.IsBlockDesign 3 4) : (e.finsetCongr.finsetCongr H).IsBlockDesign 3 4 := by
  change (H.map e.finsetCongr.toEmbedding).IsBlockDesign 3 4
  rw [map_eq_image]
  exact PointedProduct.relabel_design e hH

variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}

/-- A zero switch adds one independent binary parity check. -/
def zeroCheckEquiv [Nonempty V] (hH : H.IsBlockDesign 3 4) :
    Checks H × ZMod 2 ≃ Checks (doubling hH (fun _ => false)) := by
  let F (p : Checks H × ZMod 2) : Checks (doubling hH (fun _ => false)) :=
    ⟨liftCheck p.1.val p.2,(check_lift_iff ..).mpr fun i => by simp [p.1.prop i.val i.prop,bitValue]⟩
  apply Equiv.ofBijective F
  constructor
  · rintro ⟨u,c⟩ ⟨v,b⟩ he
    have ev (x : V) (i : Bool) := congrArg (fun z : Checks (doubling hH (fun _ => false)) => z.val (x,i)) he
    have eq : u=v := Subtype.ext (funext fun x => by simpa [F,liftCheck,bitValue] using ev x false)
    subst v
    have eqc := ev (Classical.choice inferInstance) true
    simpa [F,liftCheck,bitValue] using eqc
  · rintro ⟨g,hg⟩
    obtain ⟨u,c,rfl,hs⟩ := (check_decomposition hH _ g).mp hg
    have hc : Check H u := fun B hB => by simpa [bitValue] using hs ⟨B,hB⟩
    exact ⟨(⟨u,hc⟩,c),rfl⟩

theorem zeroSwitch_separates [Nonempty V] (hH : H.IsBlockDesign 3 4) (sep : Separates H) :
    Separates (doubling hH (fun _ => false)) :=
  (separating_iff hH sep _).mpr ⟨fun _ => 0,fun i => by simp [blockSum,bitValue]⟩

def binaryStepLabels (d : ℕ) : Fin (2^d) × Bool ≃ Fin (2^(d+1)) :=
  Fintype.equivOfCardEq (by simp [pow_succ])

/-- Starting from one point, always take the even sheets and relabel onto the ordinary finite set. -/
def binaryBase : (d : ℕ) → {H : Finset (Finset (Fin (2^d))) // H.IsBlockDesign 3 4}
  | 0 => ⟨∅,fun B hB => (notMem_empty B hB).elim,fun T ht => by
      have cap := card_le_univ T
      rw [Fintype.card_fin] at cap
      omega⟩
  | d+1 =>
    let prev := binaryBase d
    ⟨_,relabel_quadruples (binaryStepLabels d) (doubling_design prev.prop (fun _ => false))⟩

theorem binaryBase_separates (d : ℕ) : Separates (binaryBase d).val := by
  induction d with
  | zero => exact fun x y _ => Fin.ext (by have := x.isLt; have := y.isLt; omega)
  | succ d ih =>
    exact (separates_relabel (binaryStepLabels d) _).mpr (zeroSwitch_separates (binaryBase d).prop ih)

theorem binaryBase_checks (d : ℕ) : Nat.card (Checks (binaryBase d).val)=2^(d+1) := by
  classical
  induction d with
  | zero =>
    have e : Checks (binaryBase 0).val ≃ (Fin (2^0) → ZMod 2) :=
      Equiv.subtypeUnivEquiv fun f B hB => (notMem_empty B hB).elim
    rw [Nat.card_congr e]; simp [Nat.card_eq_fintype_card]
  | succ d ih =>
    let H := binaryBase d
    change Nat.card (Checks ((binaryStepLabels d).finsetCongr.finsetCongr (doubling H.prop (fun _ => false))))=_
    rw [Nat.card_congr (checkRelabel (binaryStepLabels d) (doubling H.prop (fun _ => false))),
      ← Nat.card_congr (zeroCheckEquiv H.prop),Nat.card_prod]
    have two : Nat.card (ZMod 2)=2 := by simp [Nat.card_eq_fintype_card]
    rw [two,show Nat.card (Checks H.val)=2^(d+1) from ih,pow_succ (2:ℕ) (d+1)]

#print axioms Checks
#print axioms checkRelabel
#print axioms relabel_quadruples
#print axioms zeroCheckEquiv
#print axioms zeroSwitch_separates
#print axioms binaryStepLabels
#print axioms binaryBase
#print axioms binaryBase_separates
#print axioms binaryBase_checks
end
end Erdos722.QuadSwitch
