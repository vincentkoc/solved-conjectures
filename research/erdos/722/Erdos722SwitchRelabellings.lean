import Erdos722DoubleFibrePermutations
import Erdos722CountCompatibleDoublings

/-! # The block equations for a base relabelling and independent fibre flips -/

namespace Erdos722.QuadSwitch
open Finset Equiv Function
noncomputable section
variable {V : Type*} [DecidableEq V] {H : Finset (Finset V)}

theorem footprint_fibrePerm (σ : Perm V) (f : V → Bool) (D : Finset (V × Bool)) :
    footprint ((fibrePerm σ f).finsetCongr D)=σ.finsetCongr (footprint D) := by
  simp only [footprint,Equiv.finsetCongr_apply,map_eq_image,image_image]
  rfl

theorem component_iff_parity (hH : H.IsBlockDesign 3 4) (i : H) (b : Bool) (D : Finset (V × Bool)) :
    D∈component hH i b ↔ D.card=4 ∧ footprint D=i.val ∧ blockSum (fun x : V × Bool => bitValue x.2) D=bitValue b := by
  constructor
  · intro hd
    exact ⟨(component_shape hH i hd).1,(component_shape hH i hd).2,component_parity hH i hd⟩
  · rintro ⟨hc,hp,hb⟩
    let j := chart i.val (hH.1 _ i.prop)
    have hs := tile_exhaust j hc (hp.trans (chart_range ..).symm)
    have matchBit (a : Bool) (h : D∈tile j a) : a=b :=
      (show Injective bitValue by decide) ((component_parity hH i h).symm.trans hb)
    rcases mem_union.mp hs with h|h
    · exact matchBit false h ▸ h
    · exact matchBit true h ▸ h

omit [DecidableEq V] in
theorem map_twins (σ : Perm V) (f : V → Bool) (P : Finset V) :
    (fibrePerm σ f).finsetCongr (twins P)=twins (σ.finsetCongr P) := by
  ext ⟨x,b⟩
  constructor
  · intro h
    obtain ⟨⟨y,c⟩,hy,he⟩ := mem_map.mp h
    exact mem_product.mpr ⟨mem_map.mpr ⟨y,(mem_product.mp hy).1,congrArg Prod.fst he⟩,mem_univ _⟩
  · intro h
    obtain ⟨y,hy,hyx⟩ := mem_map.mp (mem_product.mp h).1
    refine mem_map.mpr ⟨(y,b ^^ f y),mem_product.mpr ⟨hy,mem_univ _⟩,?_⟩
    exact Prod.ext hyx (by simp [fibrePerm])

theorem map_component_sum (hH : H.IsBlockDesign 3 4) (i : H) (b : Bool) {D : Finset (V × Bool)}
    (hd : D∈component hH i b) (σ : Perm V) (f : V → Bool) :
    blockSum (fun x : V × Bool => bitValue x.2) ((fibrePerm σ f).finsetCongr D) =
      blockSum (bitValue ∘ f) i.val+bitValue b := by
  rw [Equiv.finsetCongr_apply,blockSum,sum_map]
  have funEq (x : V × Bool) : bitValue ((fibrePerm σ f) x).2=liftCheck (bitValue ∘ f) 1 x := by
    simp [fibrePerm,bit_xor,liftCheck,add_comm]
  simp only [Equiv.toEmbedding_apply,funEq]
  exact (component_lift_sum hH i hd _ _).trans (by simp)

/-- Each base block and its switch equation are carried to a target block.
Block membership is part of the condition on the underlying point permutation. -/
def Matches {V : Type*} {H : Finset (Finset V)} (s t : H → Bool) (σ : Perm V) (f : V → Bool) :=
  ∀ i : H, ∃ j : H, σ.finsetCongr i.val=j.val ∧ bitValue (t j)=blockSum (bitValue ∘ f) i.val+bitValue (s i)

variable [Fintype V]

theorem maps_doubling_iff (hH : H.IsBlockDesign 3 4) (s t : H → Bool) (σ : Perm V) (f : V → Bool) :
    (fibrePerm σ f).finsetCongr.finsetCongr (doubling hH s)=doubling hH t ↔ Matches s t σ f := by
  let e := fibrePerm σ f
  constructor
  · intro he i
    obtain ⟨D,hD⟩ := card_pos.mp (show 0<(component hH i (s i)).card by rw [component,tile_card]; decide)
    have src := (mem_doubling hH s D).mpr (.inr ⟨i,hD⟩)
    have dest : e.finsetCongr D∈doubling hH t := he ▸ mem_map.mpr ⟨D,src,rfl⟩
    have proj : footprint (e.finsetCongr D)=σ.finsetCongr i.val :=
      (footprint_fibrePerm σ f D).trans (congrArg σ.finsetCongr (component_shape hH i hD).2)
    rcases (mem_doubling hH t _).mp dest with ⟨P,hp,heq⟩|⟨j,hj⟩
    · rw [← heq,footprint_twins] at proj
      have hc := congrArg Finset.card proj
      simp only [Equiv.finsetCongr_apply,card_map,hp,hH.1 i.val i.prop] at hc
      exact False.elim ((by decide : (2:ℕ)≠4) hc)
    · exact ⟨j,proj.symm.trans (component_shape hH j hj).2,
        (component_parity hH j hj).symm.trans (map_component_sum hH i _ hD σ f)⟩
  · intro h
    apply eq_of_subset_of_card_le
    · intro D hD
      obtain ⟨B,hB,rfl⟩ := mem_map.mp hD
      rcases (mem_doubling hH s _).mp hB with ⟨P,hP,rfl⟩ | ⟨i,hi⟩
      · apply (mem_doubling hH t _).mpr
        exact .inl ⟨σ.finsetCongr P,by simpa [Equiv.finsetCongr_apply] using hP,(map_twins σ f P).symm⟩
      · obtain ⟨j,he,hbit⟩ := h i
        apply (mem_doubling hH t _).mpr
        refine .inr ⟨j,(component_iff_parity hH j _ _).mpr ⟨?_,?_,?_⟩⟩
        · exact (card_map _).trans (component_shape hH i hi).1
        · exact (footprint_fibrePerm σ f _).trans ((congrArg σ.finsetCongr (component_shape hH i hi).2).trans he)
        · exact (map_component_sum hH i _ hi σ f).trans hbit.symm
    · simp only [Equiv.finsetCongr_apply,card_map,base_block_count (doubling_design hH s),
        base_block_count (doubling_design hH t),le_refl]

#print axioms footprint_fibrePerm
#print axioms component_iff_parity
#print axioms map_twins
#print axioms map_component_sum
#print axioms Matches
#print axioms maps_doubling_iff
end
end Erdos722.QuadSwitch
