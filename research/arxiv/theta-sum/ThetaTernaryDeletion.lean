import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-! Pointwise deletion estimates for ordered three-term prime representations. -/
namespace Arxiv.«2501.03234».ThetaTernaryDeletion
open Finset

def triples (A B C : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (A ×ˢ (B ×ˢ C)).filter (fun t => t.1+t.2.1+t.2.2=n)

theorem mem {A B C : Finset ℕ} {n : ℕ} {t : ℕ × ℕ × ℕ} :
    t∈triples A B C n ↔ t.1∈A ∧ t.2.1∈B ∧ t.2.2∈C ∧ t.1+t.2.1+t.2.2=n := by
  simp only [triples,mem_filter,mem_product];tauto

private theorem first_two (A B C : Finset ℕ) (n : ℕ) :
    (triples A B C n).card ≤ A.card*B.card := by
  rw [←card_product]
  apply card_le_card_of_injOn (fun t : ℕ × ℕ × ℕ => (t.1,t.2.1))
  · intro t ht;exact mem_product.mpr ⟨(mem.mp ht).1,(mem.mp ht).2.1⟩
  · rintro ⟨a,b,c⟩ hx ⟨d,e,f⟩ hy he
    obtain ⟨_,_,_,hs⟩ := mem.mp hx
    obtain ⟨_,_,_,ht⟩ := mem.mp hy
    change (a,b)=(d,e) at he
    cases he
    simp only at hs ht
    have hc : c=f := by omega
    subst f;rfl

private theorem last_two (A B C : Finset ℕ) (n : ℕ) :
    (triples A B C n).card ≤ B.card*C.card := by
  rw [←card_product]
  apply card_le_card_of_injOn (fun t : ℕ × ℕ × ℕ => t.2)
  · intro t ht;exact mem_product.mpr ⟨(mem.mp ht).2.1,(mem.mp ht).2.2.1⟩
  · rintro ⟨a,b,c⟩ hx ⟨d,e,f⟩ hy he
    obtain ⟨_,_,_,hs⟩ := mem.mp hx
    obtain ⟨_,_,_,ht⟩ := mem.mp hy
    change (b,c)=(e,f) at he
    cases he
    simp only at hs ht
    have ha : a=d := by omega
    subst d;rfl

def distinctTriples (A : Finset ℕ) (n : ℕ) :=
  (triples A A A n).filter (fun t => t.1≠t.2.1 ∧ t.1≠t.2.2 ∧ t.2.1≠t.2.2)

theorem deletion (A E : Finset ℕ) (n : ℕ) :
    (triples A A A n).card ≤ (triples (A \ E) (A \ E) (A \ E) n).card+3*E.card*A.card := by
  let R := triples (A \ E) (A \ E) (A \ E) n
  let F := triples E A A n
  let G := triples A E A n
  let H := triples A A E n
  have hsub : triples A A A n ⊆ ((R∪F)∪G)∪H := by
    intro t ht
    obtain ⟨ha,hb,hc,hh⟩ := mem.mp ht
    simp only [mem_union]
    by_cases h₁ : t.1∈E
    · exact Or.inl (Or.inl (Or.inr (mem.mpr ⟨h₁,hb,hc,hh⟩)))
    by_cases h₂ : t.2.1∈E
    · exact Or.inl (Or.inr (mem.mpr ⟨ha,h₂,hc,hh⟩))
    by_cases h₃ : t.2.2∈E
    · exact Or.inr (mem.mpr ⟨ha,hb,h₃,hh⟩)
    exact Or.inl (Or.inl (Or.inl (mem.mpr ⟨mem_sdiff.mpr ⟨ha,h₁⟩,mem_sdiff.mpr ⟨hb,h₂⟩,mem_sdiff.mpr ⟨hc,h₃⟩,hh⟩)))
  have hf := first_two E A A n
  have hg := first_two A E A n
  have hh := last_two A A E n
  change F.card≤_ at hf
  change G.card≤_ at hg
  change H.card≤_ at hh
  rw [Nat.mul_comm A.card E.card] at hg hh
  change _ ≤ R.card+3*E.card*A.card
  have h := (card_le_card hsub).trans (card_union_le _ _)
  have h' := card_union_le (R∪F) G
  have h'' := card_union_le R F
  nlinarith only [h,h',h'',hf,hg,hh]

theorem diagonal (A : Finset ℕ) (n : ℕ) :
    (triples A A A n).card ≤ (distinctTriples A n).card+3*A.card := by
  let D := distinctTriples A n
  let F := A.image (fun a => (a,a,n-2*a))
  let G := A.image (fun a => (a,n-2*a,a))
  let H := A.image (fun a => (n-2*a,a,a))
  have hsub : triples A A A n ⊆ ((D∪F)∪G)∪H := by
    rintro ⟨a,b,c⟩ ht
    obtain ⟨ha,hb,hc,hh⟩ := mem.mp ht
    change a+b+c=n at hh
    simp only [mem_union]
    by_cases hab : a=b
    · subst b
      exact Or.inl (Or.inl (Or.inr (mem_image.mpr ⟨a,ha,by rw [show n-2*a=c by omega]⟩)))
    by_cases hac : a=c
    · subst c
      exact Or.inl (Or.inr (mem_image.mpr ⟨a,ha,by rw [show n-2*a=b by omega]⟩))
    by_cases hbc : b=c
    · subst c
      exact Or.inr (mem_image.mpr ⟨b,hb,by rw [show n-2*b=a by omega]⟩)
    exact Or.inl (Or.inl (Or.inl (mem_filter.mpr ⟨ht,hab,hac,hbc⟩)))
  have hl := (card_le_card hsub).trans (card_union_le _ _)
  have h₁ := card_union_le (D∪F) G
  have h₂ := card_union_le D F
  have hf : F.card≤A.card := card_image_le
  have hg : G.card≤A.card := card_image_le
  have hh : H.card≤A.card := card_image_le
  change _≤D.card+3*A.card
  omega

theorem distinct_deletion (A E : Finset ℕ) (n : ℕ) :
    (triples A A A n).card ≤ (distinctTriples (A \ E) n).card+3*(E.card+1)*A.card := by
  have h := deletion A E n
  have hd := diagonal (A \ E) n
  have ha : (A \ E).card ≤ A.card := card_le_card sdiff_subset
  nlinarith only [h,hd,ha]

#print axioms diagonal
#print axioms distinct_deletion
#print axioms deletion
end Arxiv.«2501.03234».ThetaTernaryDeletion
