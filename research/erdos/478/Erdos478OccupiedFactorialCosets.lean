import Erdos478FactorialCosetProfiles

/-! # Cosets occupied by a moving factorial window or prescribed three-term visits -/

namespace Erdos478.CyclotomicProfiles
open Finset
open scoped Classical
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def occupied (H : Subgroup (ZMod p)ˣ) (a b : ℕ) := (Icc a b).image (factorialLabel H)

def completeVisits (H : Subgroup (ZMod p)ˣ) (a b : ℕ) (S : Finset ((ZMod p)ˣ ⧸ H)) :=
  (Ico a (b-1)).filter fun i =>
    factorialLabel H i∈S ∧ factorialLabel H (i+1)∈S ∧ factorialLabel H (i+2)∈S

theorem visits_bound (H : Subgroup (ZMod p)ˣ) (a b : ℕ) (valid : b<p) (S : Finset ((ZMod p)ˣ ⧸ H)) :
    let T := (completeVisits H a b S).card
    T^2≤(relativeTriples S).card*(T+(Nat.card H-1)*(Nat.card H-2)) := by
  apply factorial_profiles
  · intro i h
    have := (mem_Ico.mp (mem_filter.mp h).1).2
    omega
  · intro i h
    exact (mem_filter.mp h).2

/-- In an arbitrary closed interval before p the two-step profiles distinguish factorial cosets.
The bound includes intervals with fewer than three indices. -/
theorem occupied_bound (H : Subgroup (ZMod p)ˣ) (a b : ℕ) (valid : b<p) :
    (b-a-1)^2 ≤ (occupied H a b).card^3*((b-a-1)+(Nat.card H-1)*(Nat.card H-2)) := by
  let S := occupied H a b
  let A := Ico a (b-1)
  have val (i) (hi : i∈A) : i+2≤b := by have := (mem_Ico.mp hi).2; omega
  have hit (i) (hi : i∈A) : factorialLabel H i∈S ∧ factorialLabel H (i+1)∈S ∧ factorialLabel H (i+2)∈S := by
    have lo := (mem_Ico.mp hi).1
    have high := val i hi
    have mem (j) (h1 : a≤j) (h2 : j≤b) : factorialLabel H j∈S := mem_image_of_mem _ (mem_Icc.mpr ⟨h1,h2⟩)
    exact ⟨mem _ lo (by omega),mem _ (by omega) (by omega),mem _ (by omega) high⟩
  have bound := factorial_profiles H A S (fun i h => (val i h).trans_lt valid) hit
  have card : A.card=b-a-1 := by rw [show A=Ico a (b-1) from rfl,Nat.card_Ico];omega
  rw [card] at bound
  exact bound.trans (Nat.mul_le_mul_right _ (relative_card S))

#print axioms occupied
#print axioms completeVisits
#print axioms visits_bound
#print axioms occupied_bound
end
end Erdos478.CyclotomicProfiles
