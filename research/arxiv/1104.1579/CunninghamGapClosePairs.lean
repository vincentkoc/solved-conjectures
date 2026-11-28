import Mathlib

/-! A triangularly weighted pair inequality for finite sets of natural numbers. -/

namespace CunninghamChain.GapWindow
open Finset

/-- Number of translates of a length-H interval containing both sites, with the smaller site first. -/
def weight (H a b : ℕ) := if a<b then H-(b-a) else 0

def pairWeight (H : ℕ) (A B : Finset ℕ) := ∑ a∈A, ∑ b∈B, weight H a b

private def tag (H a j : ℕ) := if a≤j ∧ j<a+H then 1 else 0

private lemma overlap {N a b : ℕ} (ha : a≤N) (H : ℕ) :
    ∑ j∈range (N+H), tag H a j * tag H b j = min a b+H-max a b := by
  let Q (j : ℕ) := (a≤j ∧ j<a+H) ∧ (b≤j ∧ j<b+H)
  have filt : (range (N+H)).filter Q = Ico (max a b) (min a b+H) := by
    ext j
    simp only [mem_filter,mem_range,mem_Ico,Q]
    omega
  rw [←Nat.card_Ico,←filt,card_filter]
  apply sum_congr rfl
  intro j _
  simp only [tag]
  split_ifs <;> omega

/-- A finite lower bound for close pairs. Every seed in A lies in [0,N]. -/
theorem close_pairs (A : Finset ℕ) {N : ℕ} (inside : ∀ a∈A, a≤N) (H : ℕ) :
    (H*A.card)^2 ≤ (N+H)*(H*A.card+2*pairWeight H A A) := by
  let C (j : ℕ) := ∑ a∈A, tag H a j
  have first : ∑ j∈range (N+H), C j = H*A.card := by
    dsimp only [C]
    rw [sum_comm]
    have one (a) (ha : a∈A) : ∑ j∈range (N+H), tag H a j = H := by
      have z := overlap (b:=a) (inside a ha) H
      have idem (j) : tag H a j * tag H a j = tag H a j := by unfold tag;split <;> decide
      simpa only [idem,min_self,max_self,Nat.add_sub_cancel_left] using z
    simpa [Nat.mul_comm] using sum_congr (s₁:=A) rfl one
  have second : ∑ j∈range (N+H), (C j)^2 = H*A.card+2*pairWeight H A A := by
    have expand (j) : C j^2 = ∑ a∈A, ∑ b∈A, tag H a j*tag H b j := by
      simp [C,pow_two,sum_mul,mul_sum]
      exact sum_comm
    simp_rw [expand]
    rw [sum_comm]
    have per (a) (ha : a∈A) :
        ∑ j∈range (N+H), ∑ b∈A, tag H a j * tag H b j =
        ∑ b∈A, ((if a=b then H else 0)+weight H a b+weight H b a) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro b _
      rw [overlap (inside a ha)]
      unfold weight
      split_ifs <;> omega
    rw [sum_congr rfl per]
    simp only [sum_add_distrib]
    have diag : ∑ a∈A, ∑ b∈A, (if a=b then H else 0) = H*A.card := by
      simp [Nat.mul_comm]
    rw [diag]
    unfold pairWeight
    rw [show (∑ a∈A, ∑ b∈A, weight H b a) = ∑ a∈A, ∑ b∈A, weight H a b from sum_comm]
    omega
  have cs := sq_sum_le_card_mul_sum_sq (s:=range (N+H)) (f:=C)
  simpa only [first,second,card_range,Nat.cast_id] using cs

#print axioms close_pairs

end CunninghamChain.GapWindow
