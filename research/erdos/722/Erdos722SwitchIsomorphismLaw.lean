import Erdos722SwitchRelabellings

/-! # Unrestricted isomorphism and the kernel of the action on the base -/

namespace Erdos722.QuadSwitch
open Finset Equiv Function
noncomputable section
variable {V : Type*} {H : Finset (Finset V)}

theorem matches_preserves {s t : H → Bool} {σ : Perm V} {f : V → Bool} (h : Matches s t σ f) :
    σ.finsetCongr.finsetCongr H=H := by
  apply eq_of_subset_of_card_le
  · intro B hB
    obtain ⟨A,hA,rfl⟩ := mem_map.mp hB
    obtain ⟨j,he,_⟩ := h ⟨A,hA⟩
    exact he.symm ▸ j.prop
  · simp [Equiv.finsetCongr_apply]

def blockPerm (σ : Perm V) (hs : σ.finsetCongr.finsetCongr H=H) : Perm H :=
  σ.finsetCongr.subtypeEquiv fun B => by
    constructor
    · intro h
      exact hs ▸ mem_map.mpr ⟨B,h,rfl⟩
    · intro h
      rw [← hs] at h
      obtain ⟨A,hA,he⟩ := mem_map.mp h
      exact σ.finsetCongr.injective he ▸ hA

theorem matches_iff_equations (s t : H → Bool) (σ : Perm V) (f : V → Bool) (hs : σ.finsetCongr.finsetCongr H=H) :
    Matches s t σ f ↔ ∀ i : H, bitValue (t (blockPerm σ hs i))=blockSum (bitValue ∘ f) i.val+bitValue (s i) := by
  constructor
  · intro h i
    obtain ⟨j,he,hb⟩ := h i
    exact (show j=blockPerm σ hs i from Subtype.ext he.symm) ▸ hb
  · exact fun h i => ⟨blockPerm σ hs i,rfl,h i⟩

variable [Fintype V] [DecidableEq V] [Nonempty V]

/-- Over a base distinguished by its checks, every isomorphism class of
doubles is one orbit of base permutations and block sums of point switches. -/
theorem isomorphic_iff_matches (hH : H.IsBlockDesign 3 4) (sep : Separates H) (s t : H → Bool) :
    Isomorphic (doubling hH s) (doubling hH t) ↔ ∃ (σ : Perm V) (f : V → Bool), Matches s t σ f := by
  constructor
  · intro iso
    by_cases cs : Coboundary s
    · obtain ⟨u,hu⟩ := cs
      obtain ⟨v,hv⟩ := (isomorphic_coboundary hH sep iso).mp ⟨u,hu⟩
      let f (x : V) := decide (u x+v x=1)
      have point (x : V) : bitValue (f x)=u x+v x :=
        (show ∀ a : ZMod 2, bitValue (decide (a=1))=a by decide) _
      refine ⟨Equiv.refl _,f,fun i => ⟨i,by simp,?_⟩⟩
      rw [← hu i,← hv i]
      unfold blockSum
      simp only [comp_apply,point,sum_add_distrib]
      rw [add_right_comm,CharTwo.add_self_eq_zero,zero_add]
    · obtain ⟨e,he⟩ := iso
      obtain ⟨σ,f,rfl⟩ := intrinsic_isomorphism hH sep cs e he
      exact ⟨σ,f,(maps_doubling_iff hH s t σ f).mp he⟩
  · rintro ⟨σ,f,h⟩
    exact ⟨fibrePerm σ f,(maps_doubling_iff hH s t σ f).mpr h⟩

omit [Nonempty V] in
theorem vertical_iff_check (hH : H.IsBlockDesign 3 4) (s : H → Bool) (f : V → Bool) :
    (fibrePerm (Equiv.refl V) f).finsetCongr.finsetCongr (doubling hH s)=doubling hH s ↔ Check H (bitValue ∘ f) := by
  rw [maps_doubling_iff]
  constructor
  · intro h B hB
    let i : H := ⟨B,hB⟩
    obtain ⟨j,he,hbit⟩ := h i
    have eq : i=j := Subtype.ext (by simpa using he)
    subst j
    exact add_right_cancel (show blockSum (bitValue ∘ f) B+bitValue (s i)=0+bitValue (s i) by simpa using hbit.symm)
  · exact fun h i => ⟨i,by simp,by rw [h i.val i.prop,zero_add]⟩

#print axioms matches_preserves
#print axioms blockPerm
#print axioms matches_iff_equations
#print axioms isomorphic_iff_matches
#print axioms vertical_iff_check
end
end Erdos722.QuadSwitch
