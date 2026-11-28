import Mathlib.Data.Finset.Prod
import Mathlib.Data.Sym.Card
import Mathlib.Tactic

/-! # Counting a commutative image with two overlapping argument sets -/

namespace Erdos478.ParityProducts
open Finset
open scoped Classical
noncomputable section

def mixedImage {α β : Type*} (f : α → α → β) (E O : Finset α) : Finset β :=
  (E ×ˢ O).image (fun q => f q.1 q.2)

/-- Each pair of distinct common elements supplies two orders in the
rectangle with the same value. One order may be discarded for every pair. -/
theorem mixed_image_bound {α β : Type*} [LinearOrder α] [DecidableEq α] (f : α → α → β)
    (sym : ∀ x y,f x y=f y x) (E O : Finset α) :
    (mixedImage f E O).card+(E∩O).card.choose 2 ≤ E.card*O.card := by
  let I := E∩O
  let T := (I ×ˢ I).filter (fun q => q.1<q.2)
  have small : T⊆E ×ˢ O := by
    intro q h
    obtain ⟨h₁,h₂⟩ := mem_product.mp (mem_filter.mp h).1
    exact mem_product.mpr ⟨(mem_inter.mp h₁).1,(mem_inter.mp h₂).2⟩
  have covers : mixedImage f E O ⊆ ((E ×ˢ O) \ T).image (fun q => f q.1 q.2) := by
    intro v hv
    obtain ⟨⟨x,y⟩,hxy,rfl⟩ := mem_image.mp hv
    by_cases ht : (x,y)∈T
    · obtain ⟨a,b⟩ := mem_product.mp (mem_filter.mp ht).1
      have lt : x<y := (mem_filter.mp ht).2
      have no : (y,x)∉T := fun h => lt_asymm lt (mem_filter.mp h).2
      exact mem_image.mpr ⟨(y,x),mem_sdiff.mpr
        ⟨mem_product.mpr ⟨(mem_inter.mp b).1,(mem_inter.mp a).2⟩,no⟩,sym y x⟩
    · exact mem_image.mpr ⟨(x,y),mem_sdiff.mpr ⟨hxy,ht⟩,rfl⟩
  have c := (card_le_card covers).trans card_image_le
  have part := card_sdiff_add_card_eq_card small
  have sz : T.card=I.card.choose 2 := card_product_filter_lt
  rw [card_product,sz] at part
  change _+I.card.choose 2≤_
  omega

#print axioms mixedImage
#print axioms mixed_image_bound
end
end Erdos478.ParityProducts
