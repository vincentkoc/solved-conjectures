import Erdos478ReturnCubicBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Counting short gaps with finite capacities -/

namespace Erdos478.ReturnConcentration
open Finset
open scoped Classical

/-- Pay for a gap up to a cutoff, charging only its shortfall to its degree capacity. -/
theorem cutoff {α : Type*} (s : Finset α) (g : α → ℕ) (c : ℕ → ℕ) (hc : ∀ k, (s.filter (fun i => g i = k)).card ≤ c k) (h : ℕ) :
    h*s.card ≤ (∑ i ∈ s, g i) + ∑ k ∈ range h, (h-k)*c k := by
  classical
  let w (k : ℕ) (i : α) := if g i=k then h-k else 0
  have localCost (i : α) : h ≤ g i + ∑ k ∈ range h, w k i := by
    by_cases hi : g i < h
    · simp [w,hi,Nat.add_sub_of_le hi.le]
    · exact (le_of_not_gt hi).trans (Nat.le_add_right ..)
  have totals (k : ℕ) :
      ∑ i ∈ s, w k i ≤ (h-k)*c k := by
    change (∑ i ∈ s, if g i = k then h-k else 0) ≤ _
    rw [← sum_filter]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right (h-k) (hc k)
  calc
    h*s.card = ∑ _ ∈ s,h := by simp [Nat.mul_comm]
    _ ≤ ∑ i ∈ s,(g i + ∑ k ∈ range h,w k i) := sum_le_sum fun i _ => localCost i
    _ = (∑ i ∈ s, g i) + ∑ k ∈ range h, ∑ i ∈ s, w k i := by
      rw [sum_add_distrib, Finset.sum_comm (s:=s) (t:=range h)]
    _ ≤ _ := Nat.add_le_add_left (sum_le_sum fun k _ => totals k) _

/-- At an even distance, a Wilson-reflected, disjoint copy uses the other half of the roots. -/
def reflectedCapacity (k : ℕ) := if k % 2 = 0 then k/2 else k

private theorem degrees (a : ℤ) (h : ℕ) :
    6*(∑ k ∈ range h,(a-k)*k) = (h:ℤ)*(h-1)*(3*a-2*h+1) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [sum_range_succ,mul_add,ih]
    push_cast
    ring

private theorem reflectedDegrees (a : ℤ) (t : ℕ) :
    2*(∑ k ∈ range (2*t),(a-k)*(reflectedCapacity k : ℤ)) =
      a*(3*(t:ℤ)^2-t) - 4*t^3+2*t^2 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show 2*(t+1) = (2*t+1)+1 by omega,sum_range_succ,sum_range_succ]
    have even : reflectedCapacity (2*t)=t := by simp [reflectedCapacity]
    have odd : reflectedCapacity (2*t+1)=2*t+1 := by simp [reflectedCapacity,Nat.add_mod]
    rw [even,odd,mul_add,mul_add,ih]
    push_cast
    ring

private theorem cast_cost (h : ℕ) (c : ℕ → ℕ) :
    ((∑ k ∈ range h, (h-k)*c k : ℕ) : ℤ) =
    ∑ k ∈ range h, ((h:ℤ)-k)*c k := by
  rw [Nat.cast_sum]
  apply sum_congr rfl
  intro k hk
  rw [Nat.cast_mul,Nat.cast_sub (mem_range.mp hk).le]

theorem degree_cost (h : ℕ) : 6*(∑ k ∈ range h,(h-k)*k)+h = h^3 := by
  have e := degrees (h:ℤ) h
  exact_mod_cast (show 6*((∑ k ∈ range h,(h-k)*k : ℕ) : ℤ)+h = (h:ℤ)^3 by
    rw [cast_cost h (fun k => k)]
    nlinarith)

theorem reflected_cost (t : ℕ) :
    (∑ k ∈ range (2*t),(2*t-k)*reflectedCapacity k) = t^3 := by
  have e := reflectedDegrees (2*(t:ℤ)) t
  exact_mod_cast (show ((∑ k ∈ range (2*t),(2*t-k)*reflectedCapacity k : ℕ) : ℤ) = (t:ℤ)^3 by
    rw [cast_cost (2*t) reflectedCapacity]
    push_cast
    nlinarith)

#print axioms cutoff
#print axioms reflectedCapacity
#print axioms degree_cost
#print axioms reflected_cost
end Erdos478.ReturnConcentration
