import Erdos478WindowPairIncidence

/-! # Total collision energy over every positive factorial window at a fixed prime -/

namespace Erdos478.WindowAverage
open Finset
open scoped Classical
noncomputable section

/-- Each unordered repeated pair is counted once by its two positions in the window. -/
def pairEnergy (p a H : ℕ) : ℕ :=
  ∑ s ∈ range (H+1), ∑ r ∈ range s, if (a+r).factorial%p=(a+s).factorial%p then 1 else 0

theorem sum_pairEnergy (p H : ℕ) :
    ∑ a ∈ starts p H,pairEnergy p a H=∑ s ∈ range (H+1), ∑ r ∈ range s,(equalStarts p H r s).card := by
  unfold pairEnergy
  rw [sum_comm]
  apply sum_congr rfl
  intro s _
  rw [sum_comm]
  apply sum_congr rfl
  intro r _
  simp only [equalStarts,card_filter]

private theorem gap_sum (s : ℕ) : ∑ r ∈ range s,(s-r)=(s+1).choose 2 := by
  induction s with
  | zero => decide
  | succ s ih =>
    rw [sum_range_succ']
    simp only [Nat.succ_sub_succ_eq_sub,Nat.sub_zero,ih]
    rw [Nat.choose_succ_succ (s+1) 1,Nat.choose_one_right]
    ac_rfl

private theorem all_gaps (H : ℕ) : ∑ s ∈ range (H+1), ∑ r ∈ range s,(s-r)=(H+2).choose 3 := by
  simp_rw [gap_sum]
  induction H with
  | zero => decide
  | succ H ih =>
    rw [sum_range_succ,ih,Nat.choose_succ_succ (H+2) 2]
    ac_rfl

private theorem adjacent_sum (H : ℕ) : ∑ s ∈ range (H+1), ∑ r ∈ range s,(if r+1=s then 1 else 0)=H := by
  induction H with
  | zero => decide
  | succ H ih =>
    rw [sum_range_succ,ih,sum_range_succ]
    have z : ∑ r ∈ range H,(if r+1=H+1 then 1 else 0)=0 := sum_eq_zero fun r hr =>
      if_neg (by have := mem_range.mp hr; omega)
    rw [z,if_pos rfl,zero_add]

/-- The gap-degree bound summed over pairs of window positions. The additive
term removes the diagonal of adjacent positions, which are always unequal. -/
theorem total_energy_bound {p : ℕ} (prime : p.Prime) (H : ℕ) :
    (∑ a ∈ starts p H,pairEnergy p a H)+H≤(H+2).choose 3 := by
  apply le_trans _ (all_gaps H).le
  rw [show (∑ a ∈ starts p H,pairEnergy p a H)+H=_ from congrArg₂ (·+·) (sum_pairEnergy p H) (adjacent_sum H).symm]
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro s hs
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro r hr
  have rs := mem_range.mp hr
  have sH := mem_range.mp hs
  by_cases eq : r+1=s
  · subst s
    rw [adjacent_starts_empty prime (by omega),card_empty,if_pos rfl]
    omega
  · rw [if_neg eq,add_zero]
    exact equalStarts_card_le prime rs (by omega)

#print axioms pairEnergy
#print axioms sum_pairEnergy
#print axioms total_energy_bound
end
end Erdos478.WindowAverage
