import Erdos722FieldGraphCovers
import Mathlib.Tactic

/-!
# Local covers with a singleton coordinate

A point–point rectangle has only two vertices. A line–point rectangle
has one block including infinity. A circle–point rectangle uses its
finite vertices as the unique block.
-/

namespace Erdos722.PointedProduct
open Finset Function
noncomputable section

def singleton_singleton (q : ℕ) : RectangleCover q .point .point Unit Unit := by
  refine ⟨∅,by simp,by simp,?_⟩
  intro T ht
  have h := card_le_univ T
  have h2 : Fintype.card (Grid Unit Unit)=2 := by simp [Grid]
  omega

def line_singleton (U : Type*) [Fintype U] [DecidableEq U] :
    RectangleCover (Fintype.card U) .line .point U Unit := by
  classical
  refine ⟨{univ},?_,?_,?_⟩
  · rintro B hB
    obtain rfl := mem_singleton.mp hB
    simp [Grid]
  · intro B _ T _ ht
    obtain ⟨_,⟨hp,_⟩⟩ := traces_size ht
    have hsmall := card_le_one_of_subsingleton (rightTrace T)
    have hi : Injective (Prod.fst : U × Unit → U) := fun _ _ h => Prod.ext h (Subsingleton.elim ..)
    refine ⟨?_,by change (rightTrace T).card=1; omega⟩
    change 2≤(T.eraseNone.image Prod.fst).card
    rw [card_image_of_injective _ hi]
    by_cases hn : none∈T
    · rw [card_eraseNone_of_mem hn,ht]
    · rw [card_eraseNone_of_not_mem hn,ht]
      decide
  · intro T _ _
    exact ⟨univ,⟨mem_singleton_self _,subset_univ _⟩,fun _ h => mem_singleton.mp h.1⟩

def circle_singleton {q : ℕ} (U : Type*) [Fintype U] [DecidableEq U] (hu : Fintype.card U=q+1) :
    RectangleCover q .circle .point U Unit := by
  apply word_cover hu (fun _ => True)
  · intro f _ S hs
    have hpos : S.Nonempty := card_pos.mp (by omega)
    obtain ⟨x,hx⟩ := hpos
    have hm := mem_image_of_mem (fun i : S => f i.val) (mem_univ (⟨x,hx⟩ : S))
    have hp := card_pos.mpr ⟨_,hm⟩
    have hl := card_le_one_of_subsingleton (univ.image (fun i : S => f i.val))
    change (univ.image (fun i : S => f i.val)).card=1
    omega
  · intro S _ d _
    exact ⟨fun _ => (),⟨trivial,fun _ => Subsingleton.elim ..⟩,fun _ _ => Subsingleton.elim ..⟩

#print axioms singleton_singleton
#print axioms line_singleton
#print axioms circle_singleton
end
end Erdos722.PointedProduct
