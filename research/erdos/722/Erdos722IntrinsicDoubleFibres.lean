import Erdos722QuadrupleParityChecks

/-! # Recovering the point fibres of a switched quadruple system from its parity checks -/

namespace Erdos722.QuadSwitch
open Finset Function
noncomputable section

def SameChecks {V : Type*} (D : Finset (Finset V)) (x y : V) := ∀ f, Check D f → f x=f y

def Separates {V : Type*} (D : Finset (Finset V)) := ∀ x y, SameChecks D x y → x=y

def Coboundary {V : Type*} {H : Finset (Finset V)} (bits : H → Bool) :=
  ∃ u : V → ZMod 2, ∀ i : H, blockSum u i.val=bitValue (bits i)

theorem check_relabel {V W : Type*} (e : V ≃ W) (H : Finset (Finset V)) (f : W → ZMod 2) :
    Check (e.finsetCongr.finsetCongr H) f ↔ Check H (f ∘ e) := by
  have eq (B : Finset V) : blockSum f (e.finsetCongr B)=blockSum (f ∘ e) B := by
    simp [Equiv.finsetCongr_apply,blockSum]
  constructor
  · intro h B hB
    exact (eq B) ▸ h _ (mem_map.mpr ⟨B,hB,rfl⟩)
  · intro h B hB
    obtain ⟨A,hA,rfl⟩ := mem_map.mp hB
    exact (eq A).trans (h A hA)

theorem sameChecks_relabel {V W : Type*} (e : V ≃ W) (H : Finset (Finset V)) (x y : V) :
    SameChecks H x y ↔ SameChecks (e.finsetCongr.finsetCongr H) (e x) (e y) := by
  constructor
  · intro h f hf
    exact h (f ∘ e) ((check_relabel e H f).mp hf)
  · intro h f hf
    have hg : Check (e.finsetCongr.finsetCongr H) (f ∘ e.symm) := (check_relabel ..).mpr (by simpa [Function.comp_def] using hf)
    simpa using h (f ∘ e.symm) hg

variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}

theorem base_check_lifts (hH : H.IsBlockDesign 3 4) (bits : H → Bool) {u : V → ZMod 2}
    (hu : Check H u) : Check (doubling hH bits) (fun x => u x.1) := by
  have h := (check_lift_iff hH bits u 0).mpr (fun i => by simpa using hu i.val i.prop)
  exact (show liftCheck u 0=(fun x => u x.1) by funext x; simp [liftCheck]) ▸ h

theorem sameChecks_base (hH : H.IsBlockDesign 3 4) (bits : H → Bool) {x y : V × Bool}
    (h : SameChecks (doubling hH bits) x y) : SameChecks H x.1 y.1 :=
  fun u hu => h (fun z => u z.1) (base_check_lifts hH bits hu)

/-- A fibre-splitting check exists precisely when the switch values are block sums. -/
theorem splits_fibre_iff [Nonempty V] (hH : H.IsBlockDesign 3 4) (bits : H → Bool) (x : V) :
    ¬SameChecks (doubling hH bits) (x,false) (x,true) ↔ Coboundary bits := by
  constructor
  · intro h
    unfold SameChecks at h
    push Not at h
    obtain ⟨f,hf,hne⟩ := h
    obtain ⟨u,c,rfl,hs⟩ := (check_decomposition hH bits f).mp hf
    have hc : c≠0 := by rintro rfl; simp [liftCheck] at hne
    obtain rfl := (show ∀ z : ZMod 2, z≠0 → z=1 by decide) c hc
    exact ⟨u,fun i => by simpa using hs i⟩
  · rintro ⟨u,hu⟩ h
    have hf : Check (doubling hH bits) (liftCheck u 1) :=
      (check_lift_iff hH bits u 1).mpr (fun i => by simpa using hu i)
    have he := h _ hf
    simp [liftCheck,bitValue] at he

/-- For a non-coboundary over a separating base, two labels are indistinguishable
under all binary checks exactly when they lie over the same point. -/
theorem intrinsic_fibres [Nonempty V] (hH : H.IsBlockDesign 3 4) (sep : Separates H)
    (bits : H → Bool) (ng : ¬Coboundary bits) (x y : V × Bool) :
    SameChecks (doubling hH bits) x y ↔ x.1=y.1 := by
  constructor
  · exact fun h => sep _ _ (sameChecks_base hH bits h)
  · intro he f hf
    obtain ⟨u,c,rfl,hs⟩ := (check_decomposition hH bits f).mp hf
    have hc : c=0 := by
      by_contra hn
      obtain rfl := (show ∀ z : ZMod 2, z≠0 → z=1 by decide) c hn
      exact ng ⟨u,fun i => by simpa using hs i⟩
    simp [liftCheck,hc,he]

theorem separating_iff [Nonempty V] (hH : H.IsBlockDesign 3 4) (sep : Separates H) (bits : H → Bool) :
    Separates (doubling hH bits) ↔ Coboundary bits := by
  constructor
  · intro h
    let x : V := Classical.choice inferInstance
    apply (splits_fibre_iff hH bits x).mp
    intro same
    have eq := congrArg Prod.snd (h _ _ same)
    exact Bool.false_ne_true eq
  · rintro ⟨u,hu⟩ x y h
    have he := sep _ _ (sameChecks_base hH bits h)
    have hf : Check (doubling hH bits) (liftCheck u 1) :=
      (check_lift_iff hH bits u 1).mpr (fun i => by simpa using hu i)
    have eq := h _ hf
    simp only [liftCheck,he,one_mul,add_right_inj] at eq
    exact Prod.ext he ((show Injective bitValue by decide) eq)

#print axioms SameChecks
#print axioms Separates
#print axioms Coboundary
#print axioms check_relabel
#print axioms sameChecks_relabel
#print axioms base_check_lifts
#print axioms sameChecks_base
#print axioms splits_fibre_iff
#print axioms intrinsic_fibres
#print axioms separating_iff
end
end Erdos722.QuadSwitch
