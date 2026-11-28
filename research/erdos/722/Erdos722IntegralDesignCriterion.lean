import Erdos722IntegralComplement
import Erdos722IncidenceDeletion

/-!
# Integral incidence weights in arbitrary rank

Take the link of one point, fill its rows by induction, then fill the
remaining residual on the deletion. The boundary has a direct integral
inverse on admissible vectors.
-/

namespace Erdos722.IntegralDesign
open Finset
variable {α : Type*} [DecidableEq α]

private theorem zero_rank (V : Finset α) {k : ℕ} (h : k≤V.card) (y : Finset α → ℤ) :
    ∃ w, Represents V 0 k y w := by
  obtain ⟨B,hV,hB⟩ := exists_subset_card_eq h
  refine ⟨fun A => if A=B then y ∅ else 0,?_⟩
  intro A hA
  have he : A=∅ := card_eq_zero.mp (mem_powersetCard.mp hA).2
  subst A
  simp [incidence,mem_powersetCard.mpr ⟨hV,hB⟩]

/-- Integral block weights exist exactly under all local binomial divisibilities,
for arbitrary demands on r-subsets and any ground set of size at least k+r. -/
theorem signed_criterion (V : Finset α) (r k : ℕ) (hrk : r≤k) (hv : k+r≤V.card)
    (y : Finset α → ℤ) : (∃ w, Represents V r k y w) ↔ Admissible V r k y := by
  classical
  refine ⟨fun ⟨w,h⟩ => admissible_of_represents h,?_⟩
  induction V using Finset.induction_on generalizing r k y with
  | empty =>
    have he : (∅ : Finset α).card=k+r := le_antisymm (by simp) hv
    exact boundary_weights he hrk
  | insert o U ho ih =>
    intro hy
    have hc := card_insert_of_notMem ho
    by_cases he : (insert o U).card=k+r
    · exact boundary_weights he hrk hy
    cases r with
    | zero => exact zero_rank _ (by omega) y
    | succ r =>
      cases k with
      | zero => omega
      | succ k =>
        let V := insert o U
        let link (A : Finset α) := y (insert o A)
        have hlink : Admissible U r k link := by
          intro I hI hi
          have hno : o∉I := fun h => ho (hI h)
          have h := hy (insert o I) (insert_subset_insert _ hI) (by rw [card_insert_of_notMem hno]; omega)
          rw [incidence_through ho _ _ hI,card_insert_of_notMem hno] at h
          simpa only [Nat.add_sub_add_right] using h
        obtain ⟨w₁,hw₁⟩ := ih r k (by omega) (by omega) link hlink
        let v := throughWeight o w₁
        let Y (A : Finset α) := y A-incidence V (k+1) v A
        have hy' : Admissible V (r+1) (k+1) Y := admissible_sub hy
          (admissible_of_represents (w:=v) (fun _ _ => rfl))
        have vanishes (A) (hA:A∈U.powersetCard r) : Y (insert o A)=0 := by
          dsimp only [Y,V,v]
          rw [through_weight ho _ _ (mem_powersetCard.mp hA).1,hw₁ A hA]
          exact sub_self _
        have hdel : Admissible U (r+1) (k+1) Y := by
          intro I hI hi
          have h := hy' I (hI.trans (subset_insert o U)) hi
          change _ ∣ incidence (insert o U) (r+1) Y I at h
          rwa [incidence_insert ho,incidence_zero_on vanishes,add_zero] at h
        obtain ⟨w₀,hw₀⟩ := ih (r+1) (k+1) hrk (by omega) Y hdel
        refine ⟨fun B => v B+awayWeight o w₀ B,?_⟩
        intro A hA
        have ez : incidence U (k+1) w₀ A = Y A := by
          rw [powersetCard_succ_insert ho] at hA
          rcases mem_union.mp hA with hh|hh
          · exact hw₀ A hh
          · obtain ⟨B,hB,rfl⟩ := mem_image.mp hh
            rw [incidence_outside (fun h => ho (h (mem_insert_self ..))),vanishes B hB]
        change (∑ B∈(V.powersetCard (k+1)).filter (A⊆·), (v B + awayWeight o w₀ B))=y A
        rw [sum_add_distrib]
        change incidence V (k+1) v A+incidence (insert o U) (k+1) (awayWeight o w₀) A=_
        rw [away_weight ho,ez]
        dsimp only [Y]
        omega

#print axioms signed_criterion
end Erdos722.IntegralDesign
