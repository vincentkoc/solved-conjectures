import Erdos722SubsetIncidence

/-!
# Incidence sums after deleting one point

Rows and columns through a distinguished point correspond to rows and
columns of one lower cardinality on the remaining ground set.
-/

namespace Erdos722.IntegralDesign
open Finset
variable {α : Type*} [DecidableEq α]

theorem incidence_congr {V : Finset α} {r : ℕ} {w z : Finset α → ℤ}
    (h : ∀ B∈V.powersetCard r, w B=z B) (I : Finset α) :
    incidence V r w I=incidence V r z I :=
  sum_congr rfl fun B hB => h B (mem_filter.mp hB).1

theorem incidence_zero_on {V : Finset α} {r : ℕ} {w : Finset α → ℤ}
    (h : ∀ B∈V.powersetCard r, w B=0) (I : Finset α) : incidence V r w I=0 :=
  sum_eq_zero fun B hB => h B (mem_filter.mp hB).1

theorem incidence_outside {V I : Finset α} (h : ¬I⊆V) (r : ℕ) (w : Finset α → ℤ) :
    incidence V r w I=0 := by
  exact sum_eq_zero fun B hB => False.elim (h ((mem_filter.mp hB).2.trans (mem_powersetCard.mp (mem_filter.mp hB).1).1))

theorem incidence_insert {o : α} {V : Finset α} (ho : o∉V) (r : ℕ) (w : Finset α → ℤ)
    (I : Finset α) : incidence (insert o V) (r+1) w I =
      incidence V (r+1) w I + incidence V r (fun A => w (insert o A)) (I.erase o) := by
  have hout (A : Finset α) {i} (hA : A∈V.powersetCard i) : o∉A := fun h => ho ((mem_powersetCard.mp hA).1 h)
  have hdis : Disjoint (V.powersetCard (r+1)) ((V.powersetCard r).image (insert o)) := by
    apply disjoint_left.mpr
    intro B hB hf
    obtain ⟨A,_,rfl⟩ := mem_image.mp hf
    exact hout _ hB (mem_insert_self ..)
  have hinj : Set.InjOn (fun A : Finset α => insert o A) (V.powersetCard r) := by
    intro A hA B hB h
    have he := congrArg (fun S : Finset α => S.erase o) h
    simpa [hout A hA,hout B hB] using he
  simp only [incidence,sum_filter,powersetCard_succ_insert ho,sum_union hdis,sum_image hinj,subset_insert_iff]

theorem incidence_through {o : α} {V : Finset α} (ho : o∉V) (r : ℕ) (w : Finset α → ℤ)
    {I : Finset α} (hI : I⊆V) : incidence (insert o V) (r+1) w (insert o I) =
      incidence V r (fun A => w (insert o A)) I := by
  rw [incidence_insert ho,incidence_outside (fun h => ho (h (mem_insert_self ..))),zero_add,
    erase_insert (fun he => ho (hI he))]

def throughWeight (o : α) (w : Finset α → ℤ) (B : Finset α) :=
  if o∈B then w (B.erase o) else 0

def awayWeight (o : α) (w : Finset α → ℤ) (B : Finset α) :=
  if o∈B then 0 else w B

theorem through_weight {o : α} {V : Finset α} (ho : o∉V) (r : ℕ) (w : Finset α → ℤ)
    {I : Finset α} (hI : I⊆V) : incidence (insert o V) (r+1) (throughWeight o w) (insert o I) =
      incidence V r w I := by
  rw [incidence_through ho r _ hI]
  exact incidence_congr (fun B hB => by simp [throughWeight,show o∉B from fun h => ho ((mem_powersetCard.mp hB).1 h)]) I

theorem away_weight {o : α} {V : Finset α} (ho : o∉V) (r : ℕ) (w : Finset α → ℤ)
    (I : Finset α) : incidence (insert o V) (r+1) (awayWeight o w) I = incidence V (r+1) w I := by
  rw [incidence_insert ho,incidence_zero_on (w:=fun B => awayWeight o w (insert o B))
    (fun _ _ => by simp [awayWeight]),add_zero]
  exact incidence_congr (fun B hB => by simp [awayWeight,show o∉B from fun h => ho ((mem_powersetCard.mp hB).1 h)]) I

#print axioms incidence_insert
#print axioms through_weight
#print axioms away_weight
end Erdos722.IntegralDesign
