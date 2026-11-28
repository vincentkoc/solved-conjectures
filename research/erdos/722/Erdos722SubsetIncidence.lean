import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic

/-!
# Incidence sums on a finite set

Summing the incidences of k-blocks over the r-sets through a fixed subset
counts each incident block a binomial number of times.
-/

namespace Erdos722.IntegralDesign
open Finset
variable {α : Type*} [DecidableEq α]

def incidence (V : Finset α) (r : ℕ) (y : Finset α → ℤ) (I : Finset α) : ℤ :=
  ∑ A∈(V.powersetCard r).filter (I ⊆ ·), y A

def Admissible (V : Finset α) (r k : ℕ) (y : Finset α → ℤ) : Prop :=
  ∀ I⊆V, I.card≤r → (((k-I.card).choose (r-I.card) : ℕ) : ℤ) ∣ incidence V r y I

def Represents (V : Finset α) (r k : ℕ) (y w : Finset α → ℤ) : Prop :=
  ∀ A∈V.powersetCard r, incidence V k w A=y A

theorem incidence_incidence (V I : Finset α) {r k : ℕ} (hi : I.card≤r)
    (w : Finset α → ℤ) :
    incidence V r (incidence V k w) I =
      (((k-I.card).choose (r-I.card) : ℕ) : ℤ) * incidence V k w I := by
  classical
  let rows := (V.powersetCard r).filter (I ⊆ ·)
  let d := (k-I.card).choose (r-I.card)
  have part (B : Finset α) (hB : B∈V.powersetCard k) :
      (∑ A∈rows, if A⊆B then w B else 0)=if I⊆B then (d:ℤ)*w B else 0 := by
    by_cases h : I⊆B
    · rw [if_pos h,← sum_filter,sum_const,nsmul_eq_mul]
      have he : rows.filter (· ⊆ B)=(B.powersetCard r).filter (I ⊆ ·) := by
        ext A
        simp only [rows,mem_filter,mem_powersetCard]
        have H := (mem_powersetCard.mp hB).1
        exact ⟨fun h => ⟨⟨h.2,h.1.1.2⟩,h.1.2⟩,fun h => ⟨⟨⟨h.1.1.trans H,h.1.2⟩,h.2⟩,h.1.1⟩⟩
      rw [he,card_filter_powersetCard_subset I B r h hi,(mem_powersetCard.mp hB).2]
    · rw [if_neg h]
      exact sum_eq_zero fun A hA => if_neg (fun hAB => h ((mem_filter.mp hA).2.trans hAB))
  calc
    _ = ∑ A∈rows, ∑ B∈V.powersetCard k, if A⊆B then w B else 0 := by simp [rows,incidence,sum_filter]
    _ = ∑ B∈V.powersetCard k, ∑ A∈rows, if A⊆B then w B else 0 := sum_comm
    _ = ∑ B∈V.powersetCard k, if I⊆B then (d:ℤ)*w B else 0 := sum_congr rfl part
    _ = _ := by rw [← sum_filter,incidence,mul_sum]

theorem admissible_of_represents {V : Finset α} {r k : ℕ}
    {y w : Finset α → ℤ} (h : Represents V r k y w) : Admissible V r k y := by
  intro I _ hi
  use incidence V k w I
  rw [← incidence_incidence V I hi w]
  exact sum_congr rfl fun A hA => (h A (mem_filter.mp hA).1).symm

theorem admissible_sub {V : Finset α} {r k : ℕ} {x y : Finset α → ℤ}
    (hx : Admissible V r k x) (hy : Admissible V r k y) :
    Admissible V r k (fun A => x A-y A) := by
  intro I hI hi
  simpa [incidence,sum_sub_distrib] using dvd_sub (hx I hI hi) (hy I hI hi)

#print axioms incidence_incidence
#print axioms admissible_of_represents
end Erdos722.IntegralDesign
