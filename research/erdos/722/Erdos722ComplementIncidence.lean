import Erdos722SteinerWeights
import Mathlib.Data.Nat.Choose.Sum

/-! # Complementary incidence sums for signed design weights

Inclusion-exclusion exchanges disjoint blocks with rows of the incidence
matrix. When all rows at strength t vanish, only the last term survives
on a set of size t+1.
-/

namespace Erdos722.ComplementExtension
open Finset IntegralDesign
variable {α : Type*} [DecidableEq α]

def avoiding (V : Finset α) (k : ℕ) (w : Finset α → ℤ) (A : Finset α) : ℤ :=
  ∑ B∈(V.powersetCard k).filter (Disjoint A ·), w B

theorem avoiding_eq (V A : Finset α) (k : ℕ) (w : Finset α → ℤ) :
    avoiding V k w A=∑ T∈A.powerset, (-1:ℤ)^T.card*incidence V k w T := by
  classical
  have part (B : Finset α) :
      (∑ T∈A.powerset, (-1:ℤ)^T.card*(if T⊆B then w B else 0))=
        if Disjoint A B then w B else 0 := by
    have eq : A.powerset.filter (·⊆B)=(A∩B).powerset := by
      ext T
      simp [subset_inter_iff]
    calc
      _ = (∑ T∈A.powerset.filter (·⊆B), (-1:ℤ)^T.card)*w B := by
        rw [sum_mul,sum_filter]
        apply sum_congr rfl
        intro T _
        split_ifs <;> simp_all
      _ = _ := by
        rw [eq,sum_powerset_neg_one_pow_card]
        by_cases h : Disjoint A B <;> simp [h,← disjoint_iff_inter_eq_empty]
  symm
  calc
    _ = ∑ B∈V.powersetCard k, ∑ T∈A.powerset, (-1:ℤ)^T.card*(if T⊆B then w B else 0) := by
      simp_rw [incidence,sum_filter,mul_sum]
      rw [sum_comm]
    _ = _ := by simp_rw [part]; rw [avoiding,sum_filter]

theorem lower_rows_zero {V : Finset α} {r k : ℕ} (hrk : r≤k) {w : Finset α → ℤ}
    (hw : Represents V r k (fun _ => 0) w) {I : Finset α} (hi : I.card≤r) :
    incidence V k w I=0 := by
  have h := incidence_incidence (k:=k) V I hi w
  have e : incidence V r (incidence V k w) I=0 :=
    sum_eq_zero fun A hA => hw A (mem_filter.mp hA).1
  rw [e] at h
  have nz : (((k-I.card).choose (r-I.card) : ℕ):ℤ)≠0 := by
    exact_mod_cast (Nat.choose_pos (show r-I.card≤k-I.card by omega)).ne'
  exact (mul_eq_zero.mp h.symm).resolve_left nz

theorem next_row_duality {V : Finset α} {r k : ℕ} (hrk : r≤k) {w : Finset α → ℤ}
    (hw : Represents V r k (fun _ => 0) w) {A : Finset α} (hA : A.card=r+1) :
    avoiding V k w A=(-1:ℤ)^A.card*incidence V k w A := by
  rw [avoiding_eq,sum_eq_single A]
  · intro T hT hne
    have hlt := card_lt_card ((mem_powerset.mp hT).ssubset_of_ne hne)
    rw [lower_rows_zero hrk hw (by omega),mul_zero]
  · simp

def center (V : Finset α) (r k : ℕ) (l : ℤ) (w : Finset α → ℤ) (B : Finset α) :=
  (((V.card-r).choose (k-r):ℕ):ℤ)*w B-l

theorem incidence_center {V A : Finset α} (r k : ℕ) (l : ℤ) (w : Finset α → ℤ)
    (hA : A⊆V) (hk : A.card≤k) :
    incidence V k (center V r k l w) A=
      (((V.card-r).choose (k-r):ℕ):ℤ)*incidence V k w A-
      (((V.card-A.card).choose (k-A.card):ℕ):ℤ)*l := by
  unfold incidence center
  rw [sum_sub_distrib,← mul_sum,sum_const,nsmul_eq_mul,card_filter_powersetCard_subset A V k hA hk]

theorem center_zero {V : Finset α} {r k : ℕ} (hrk : r≤k) {l : ℤ} {w : Finset α → ℤ}
    (hw : Represents V r k (fun _ => l) w) :
    Represents V r k (fun _ => 0) (center V r k l w) := by
  intro A hA
  obtain ⟨hAV,ha⟩ := mem_powersetCard.mp hA
  rw [incidence_center _ _ _ _ hAV (ha ▸ hrk),ha,hw A hA,sub_self]

#print axioms avoiding
#print axioms avoiding_eq
#print axioms lower_rows_zero
#print axioms next_row_duality
#print axioms center
#print axioms incidence_center
#print axioms center_zero
end Erdos722.ComplementExtension
