import Erdos722QuadSwitchDoubling
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two

/-! # Binary parity checks of an arbitrary switched quadruple double -/

namespace Erdos722.QuadSwitch
open Finset
noncomputable section

def bitValue (b : Bool) : ZMod 2 := if b then 1 else 0

def blockSum {V : Type*} (f : V → ZMod 2) (B : Finset V) := ∑ x∈B, f x

def Check {V : Type*} (H : Finset (Finset V)) (f : V → ZMod 2) := ∀ B∈H, blockSum f B=0

def liftCheck {V : Type*} (u : V → ZMod 2) (c : ZMod 2) (x : V × Bool) := u x.1+c*bitValue x.2

theorem bit_xor : ∀ a b : Bool, bitValue (a ^^ b)=bitValue a+bitValue b := by decide

theorem sheet_parity : ∀ b, ∀ D∈sheets b, blockSum (fun x : Label => bitValue x.2) D=bitValue b := by
  decide +kernel

variable {V : Type*} [DecidableEq V] {H : Finset (Finset V)}

omit [DecidableEq V] in
theorem blockSum_twins (f : V × Bool → ZMod 2) (P : Finset V) :
    blockSum f (twins P)=∑ x∈P, (f (x,false)+f (x,true)) := by
  unfold blockSum twins
  rw [sum_product]
  apply sum_congr rfl
  intro x _
  rw [show (univ : Finset Bool)={false,true} by decide]
  simp

omit [DecidableEq V] in
theorem component_parity (hH : H.IsBlockDesign 3 4) (i : H) {b : Bool} {D : Finset (V × Bool)}
    (hd : D∈component hH i b) : blockSum (fun x : V × Bool => bitValue x.2) D=bitValue b := by
  obtain ⟨S,hs,rfl⟩ := mem_tile.mp hd
  unfold blockSum
  rw [sum_map]
  exact sheet_parity b S hs

theorem component_lift_sum (hH : H.IsBlockDesign 3 4) (i : H) {b : Bool} {D : Finset (V × Bool)}
    (hd : D∈component hH i b) (u : V → ZMod 2) (c : ZMod 2) :
    blockSum (liftCheck u c) D=blockSum u i.val+c*bitValue b := by
  have pr : (∑ x∈D, u x.1)=blockSum u i.val := by
    rw [← (component_shape hH i hd).2,blockSum,footprint,sum_image (tile_injective hd)]
  unfold blockSum liftCheck
  rw [sum_add_distrib,← mul_sum,pr]
  exact congrArg (fun y => blockSum u i.val+c*y) (component_parity hH i hd)

variable [Fintype V]

theorem common_slope (hH : H.IsBlockDesign 3 4) (bits : H → Bool) {f : V × Bool → ZMod 2}
    (hf : Check (doubling hH bits) f) (x y : V) :
    f (x,false)+f (x,true)=f (y,false)+f (y,true) := by
  by_cases he : x=y
  · simp [he]
  have card : ({x,y} : Finset V).card=2 := by simp [he]
  have h := hf _ ((mem_doubling hH bits _).mpr (.inl ⟨_,card,rfl⟩))
  rw [blockSum_twins,sum_pair he] at h
  exact CharTwo.add_eq_zero.mp h

theorem check_lift_iff (hH : H.IsBlockDesign 3 4) (bits : H → Bool) (u : V → ZMod 2) (c : ZMod 2) :
    Check (doubling hH bits) (liftCheck u c) ↔ ∀ i : H, blockSum u i.val=c*bitValue (bits i) := by
  constructor
  · intro h i
    have card := tile_card (chart i.val (hH.1 _ i.prop)) (bits i)
    obtain ⟨D,hD⟩ := card_pos.mp (show 0<(component hH i (bits i)).card by change 0<(tile _ _).card; omega)
    have hz := h D ((mem_doubling hH bits D).mpr (.inr ⟨i,hD⟩))
    rw [component_lift_sum hH i hD] at hz
    exact CharTwo.add_eq_zero.mp hz
  · intro sums D hD
    rcases (mem_doubling hH bits D).mp hD with ⟨P,hp,rfl⟩ | ⟨i,hi⟩
    · rw [blockSum_twins]
      have same (x : V) : liftCheck u c (x,false)+liftCheck u c (x,true)=c := by
        simp [liftCheck,bitValue,← add_assoc,CharTwo.add_self_eq_zero]
      simp only [same,sum_const,hp,two_nsmul,CharTwo.add_self_eq_zero]
    · rw [component_lift_sum hH i hi,sums i,CharTwo.add_self_eq_zero]

theorem check_decomposition [Nonempty V] (hH : H.IsBlockDesign 3 4) (bits : H → Bool) (f : V × Bool → ZMod 2) :
    Check (doubling hH bits) f ↔ ∃ u c, f=liftCheck u c ∧ ∀ i : H, blockSum u i.val=c*bitValue (bits i) := by
  constructor
  · intro h
    let x₀ : V := Classical.choice inferInstance
    let c := f (x₀,false)+f (x₀,true)
    let u (x : V) := f (x,false)
    have he : f=liftCheck u c := by
      funext ⟨x,b⟩
      cases b with
      | false => simp [liftCheck,bitValue,u]
      | true =>
        change f (x,true)=f (x,false)+c*bitValue true
        have step : f (x,false)+f (x,true)=c := common_slope hH bits h x x₀
        rw [← step]
        simp [bitValue,← add_assoc,CharTwo.add_self_eq_zero]
    exact ⟨u,c,he,(check_lift_iff hH bits u c).mp (he ▸ h)⟩
  · rintro ⟨u,c,rfl,h⟩
    exact (check_lift_iff hH bits u c).mpr h

#print axioms bitValue
#print axioms blockSum
#print axioms Check
#print axioms liftCheck
#print axioms bit_xor
#print axioms sheet_parity
#print axioms blockSum_twins
#print axioms component_parity
#print axioms component_lift_sum
#print axioms common_slope
#print axioms check_lift_iff
#print axioms check_decomposition
end
end Erdos722.QuadSwitch
