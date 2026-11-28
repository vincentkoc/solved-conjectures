import Erdos478OccupiedFactorialCosets

/-! # Occupation of an arbitrary union of multiplicative cosets -/

namespace Erdos478.CyclotomicProfiles
open Finset
open scoped Classical
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def visits (H : Subgroup (ZMod p)ˣ) (a b : ℕ) (S : Finset ((ZMod p)ˣ ⧸ H)) :=
  (Icc a b).filter fun i => factorialLabel H i∈S

/-- Each missing position spoils at most three starting triples. -/
theorem three_visit_count (H : Subgroup (ZMod p)ˣ) (a b : ℕ) (S : Finset ((ZMod p)ˣ ⧸ H)) :
    3*(visits H a b S).card≤2*(Icc a b).card+2+(completeVisits H a b S).card := by
  let I := Icc a b
  let J := Ico a (b-1)
  let E := visits H a b S
  let T := completeVisits H a b S
  let M := I \ E
  let bad (s : ℕ) := J.filter fun i => factorialLabel H (i+s)∉S
  have sub (s : ℕ) (small : s≤2) : (bad s).card≤M.card := by
    apply card_le_card_of_injOn (fun i => i+s)
    · intro i hi
      obtain ⟨hj,off⟩ := mem_filter.mp hi
      obtain ⟨lo,high⟩ := mem_Ico.mp hj
      change i+s∈M
      exact mem_sdiff.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,fun h => off (mem_filter.mp h).2⟩
    · intro i _ j _ eq
      exact Nat.add_right_cancel eq
  have spoiled : J \ T ⊆ bad 0 ∪ bad 1 ∪ bad 2 := by
    intro i hi
    obtain ⟨valid,absent⟩ := mem_sdiff.mp hi
    by_contra! no
    simp only [mem_union,not_or] at no
    have ok (k : ℕ) (hk : i∉bad k) : factorialLabel H (i+k)∈S := by
      by_contra h
      exact hk (mem_filter.mpr ⟨valid,h⟩)
    exact absent (mem_filter.mpr ⟨valid,ok 0 no.1.1,ok 1 no.1.2,ok 2 no.2⟩)
  have bound := (card_le_card spoiled).trans (card_union_le ..)
  have pair := card_union_le (bad 0) (bad 1)
  have msize : M.card=I.card-E.card := card_sdiff_of_subset (filter_subset ..)
  have tsize : (J \ T).card=J.card-T.card := card_sdiff_of_subset (filter_subset ..)
  have L : E.card≤I.card := card_le_card (filter_subset ..)
  have len : I.card≤J.card+2 := by simp only [I,J,Nat.card_Icc,Nat.card_Ico]; omega
  change 3*E.card≤2*I.card+2+T.card
  have s0 := sub 0 (by decide)
  have s1 := sub 1 (by decide)
  have s2 := sub 2 (by decide)
  omega

/-- Excess occupation beyond two thirds is controlled even when the cosets are chosen after the window. -/
theorem excess_mass (H : Subgroup (ZMod p)ˣ) (a b : ℕ) (valid : b<p) (S : Finset ((ZMod p)ˣ ⧸ H)) :
    (3*(visits H a b S).card-(2*(Icc a b).card+2))^2≤
      S.card^3*((b-a-1)+(Nat.card H-1)*(Nat.card H-2)) := by
  have mass := three_visit_count H a b S
  have T := visits_bound H a b valid S
  have cut : (completeVisits H a b S).card≤b-a-1 := by
    apply le_trans (card_le_card (filter_subset ..))
    rw [Nat.card_Ico]
    omega
  calc
    _ ≤ (completeVisits H a b S).card^2 := Nat.pow_le_pow_left (by omega) 2
    _ ≤ _ := T
    _ ≤ _ := Nat.mul_le_mul (relative_card S) (Nat.add_le_add_right cut _)

#print axioms visits
#print axioms three_visit_count
#print axioms excess_mass
end
end Erdos478.CyclotomicProfiles
