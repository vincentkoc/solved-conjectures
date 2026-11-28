import Erdos478MixedProductOverlap

/-! # Counting products when a set contains pairs of opposite elements -/

namespace Erdos478.ParityProducts
open Finset
open scoped Classical
noncomputable section
variable {F : Type*} [CommRing F] [DecidableEq F]

def pairProduct : Sym2 F → F := Sym2.lift ⟨(·*·),mul_comm⟩

theorem two_choose (a : ℕ) : 2*(a+1).choose 2=a*(a+1) := by
  induction a with
  | zero => decide
  | succ a ih =>
    rw [Nat.choose_succ_succ' (a+1) 1,Nat.choose_one_right]
    nlinarith only [ih]

private theorem prod_neg_image (H : Finset F) :
    let K := H ∪ H.image Neg.neg
    K.sym2.image pairProduct ⊆ H.sym2.image pairProduct ∪ (H.sym2.image pairProduct).image Neg.neg := by
  intro K z hz
  obtain ⟨q,hq,rfl⟩ := mem_image.mp hz
  induction q using Sym2.inductionOn with
  | _ x y =>
    obtain ⟨hx,hy⟩ := mk_mem_sym2_iff.mp hq
    have prod {a b : F} (ha : a∈H) (hb : b∈H) : a*b∈H.sym2.image pairProduct :=
      mem_image.mpr ⟨s(a,b),mk_mem_sym2_iff.mpr ⟨ha,hb⟩,rfl⟩
    change x*y∈_
    rcases mem_union.mp hx with hx|hx <;> rcases mem_union.mp hy with hy|hy
    · exact mem_union_left _ (prod hx hy)
    · obtain ⟨b,hb,rfl⟩ := mem_image.mp hy
      exact mem_union_right _ (mem_image.mpr ⟨_,prod hx hb,(mul_neg ..).symm⟩)
    · obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
      exact mem_union_right _ (mem_image.mpr ⟨_,prod ha hy,(neg_mul ..).symm⟩)
    · obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hy
      simpa only [neg_mul_neg] using mem_union_left ((H.sym2.image pairProduct).image Neg.neg) (prod ha hb)

/-- A half-set of h opposite pairs saves at least h² unordered products. -/
theorem antipodal_products (A H : Finset F) (dis : Disjoint H (H.image Neg.neg))
    (sub : H ∪ H.image Neg.neg ⊆ A) :
    (A.sym2.image pairProduct).card+H.card^2 ≤ (A.card+1).choose 2 := by
  let K := H ∪ H.image Neg.neg
  have inc : K.sym2⊆A.sym2 := by
    intro q hq
    induction q using Sym2.inductionOn with
    | _ x y => exact mk_mem_sym2_iff.mpr ⟨sub (mk_mem_sym2_iff.mp hq).1,sub (mk_mem_sym2_iff.mp hq).2⟩
  have cover : A.sym2.image pairProduct ⊆ (A.sym2 \ K.sym2).image pairProduct ∪ K.sym2.image pairProduct := by
    intro v hv
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hv
    by_cases h : q∈K.sym2
    · exact mem_union_right _ (mem_image_of_mem _ h)
    · exact mem_union_left _ (mem_image_of_mem _ (mem_sdiff.mpr ⟨hq,h⟩))
  have short : (K.sym2.image pairProduct).card≤2*H.sym2.card := by
    have U := (card_le_card (prod_neg_image H)).trans (card_union_le ..)
    exact U.trans (by have a := @card_image_le _ _ _ (s:=H.sym2) (f:=pairProduct)
                      have b := @card_image_le _ _ _ (s:=H.sym2.image pairProduct) (f:=Neg.neg)
                      omega)
  have bound := (card_le_card cover).trans ((card_union_le ..).trans (Nat.add_le_add card_image_le short))
  have part := card_sdiff_add_card_eq_card inc
  have hk : K.card=2*H.card := by
    rw [show K=H ∪ H.image Neg.neg from rfl,card_union_of_disjoint dis,card_image_of_injective _ neg_injective]
    omega
  rw [card_sym2] at bound
  rw [card_sym2,card_sym2,hk] at part
  nlinarith only [bound,part,two_choose H.card,two_choose (2*H.card),two_choose A.card]

#print axioms pairProduct
#print axioms two_choose
#print axioms antipodal_products
end
end Erdos478.ParityProducts
