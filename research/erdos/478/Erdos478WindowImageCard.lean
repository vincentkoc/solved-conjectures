import Erdos478WindowRepetitions

/-! # Exact size of the factorial image on a short positive-index interval -/

namespace Erdos478.LocalSpacing
open Finset
open scoped Classical

def windowValues (p a H : ℕ) : Finset ℕ :=
  (Icc a (a+H)).image fun i => i.factorial%p

def hasRepetition (p a H : ℕ) : Prop := ∃ i j, Repetition p a H i j

private theorem distinct_values {p a H x y : ℕ} (hx : x∈Icc a (a+H)) (hy : y∈Icc a (a+H))
    (he : x.factorial%p=y.factorial%p) (xy : x≠y) :
    Repetition p a H x y ∨ Repetition p a H y x := by
  obtain h|h := lt_or_gt_of_ne xy
  · exact .inl ⟨(mem_Icc.mp hx).1,h,(mem_Icc.mp hy).2,he⟩
  · exact .inr ⟨(mem_Icc.mp hy).1,h,(mem_Icc.mp hx).2,he.symm⟩

theorem window_card_exact {p a H : ℕ} (hp : p.Prime) (hu : a+H<p) (cut : (H+2)^(H^2)<p) :
    (windowValues p a H).card=if _ : hasRepetition p a H then H else H+1 := by
  classical
  let S := Icc a (a+H)
  have c : S.card=H+1 := by simp [S,Nat.card_Icc]; omega
  by_cases hit : hasRepetition p a H
  · rw [dif_pos hit]
    obtain ⟨i,j,hij⟩ := hit
    obtain ⟨lo,lt,hi,val⟩ := hij
    have ii : i∈S := mem_Icc.mpr ⟨lo,lt.le.trans hi⟩
    have jj : j∈S := mem_Icc.mpr ⟨lo.trans lt.le,hi⟩
    have im : windowValues p a H=(S.erase j).image (fun x => x.factorial%p) := by
      apply Subset.antisymm _ (image_subset_image (erase_subset j S))
      intro b hb
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hb
      by_cases e : x=j
      · subst x; exact mem_image.mpr ⟨i,mem_erase.mpr ⟨lt.ne,ii⟩,val⟩
      · exact mem_image.mpr ⟨x,mem_erase.mpr ⟨e,hx⟩,rfl⟩
    rw [im,card_image_of_injOn,card_erase_of_mem jj,c]
    · omega
    · intro x hx y hy he
      by_contra ne
      have xx := mem_erase.mp hx
      have yy := mem_erase.mp hy
      rcases distinct_values xx.2 yy.2 he ne with h|h
      · exact yy.1 (Prod.mk.inj (unique_repetition hp hu cut h ⟨lo,lt,hi,val⟩)).2
      · exact xx.1 (Prod.mk.inj (unique_repetition hp hu cut h ⟨lo,lt,hi,val⟩)).2
  · rw [dif_neg hit,windowValues,card_image_of_injOn]
    · exact c
    · intro x hx y hy he
      by_contra ne
      rcases distinct_values hx hy he ne with h|h
      · exact hit ⟨x,y,h⟩
      · exact hit ⟨y,x,h⟩

theorem window_card_bounds {p a H : ℕ} (hp : p.Prime) (hu : a+H<p) (cut : (H+2)^(H^2)<p) :
    H≤(windowValues p a H).card ∧ (windowValues p a H).card≤H+1 := by
  rw [window_card_exact hp hu cut]
  split <;> omega

#print axioms windowValues
#print axioms hasRepetition
#print axioms window_card_exact
#print axioms window_card_bounds
end Erdos478.LocalSpacing
