import Erdos722ProjectiveQuadraticWords
import Erdos722FieldGraphCovers

/-!
# The circle–line cover over a finite field

Delete the constant words from the extended quadratic evaluation code.
A word meeting a constant in three positions would equal that constant.
-/

namespace Erdos722.PointedProduct
open Finset Function
noncomputable section

def quadratic_circle_line (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    RectangleCover (Fintype.card F) .circle .line (Option F) F := by
  classical
  let h := (Quadratic.denominator F).choose
  obtain ⟨hm,hd,hn⟩ := (Quadratic.denominator F).choose_spec
  let words (f : Option F → F) := (∃ v, Quadratic.word h v=f) ∧ ¬∃ c, ∀ x, f x=c
  apply word_cover Fintype.card_option words
  · rintro f ⟨⟨v,rfl⟩,nc⟩ S hs
    change 2≤_
    by_contra! short
    obtain ⟨c,hc⟩ := card_le_one_iff_subset_singleton.mp (Nat.le_of_lt_succ short)
    obtain ⟨w,hw⟩ := Quadratic.constant_word h hm hd hn c
    have eqv : v=w := (Quadratic.restriction_bijective h hn S hs).injective (funext fun x => by
      exact (mem_singleton.mp (hc (mem_image_of_mem _ (mem_univ x)))).trans (hw x).symm)
    exact nc ⟨c,eqv ▸ hw⟩
  · intro S hs d rich
    obtain ⟨v,hv⟩ := (Quadratic.restriction_bijective h hn S hs).surjective d
    refine ⟨Quadratic.word h v,⟨⟨⟨v,rfl⟩,?_⟩,congrFun hv⟩,?_⟩
    · rintro ⟨c,hc⟩
      have hsmall : univ.image d⊆{c} := by
        intro y hy
        obtain ⟨x,_,rfl⟩ := mem_image.mp hy
        exact mem_singleton.mpr ((congrFun hv x).symm.trans (hc x))
      have hle := card_le_one_iff_subset_singleton.mpr ⟨c,hsmall⟩
      change 2≤(univ.image d).card at rich
      omega
    · rintro f ⟨⟨⟨w,rfl⟩,_⟩,hw⟩
      exact congrArg (Quadratic.word h) ((Quadratic.restriction_bijective h hn S hs).injective
        ((funext hw).trans hv.symm))

#print axioms quadratic_circle_line
end
end Erdos722.PointedProduct
