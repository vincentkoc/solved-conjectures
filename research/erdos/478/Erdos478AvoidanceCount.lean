import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Counting bounded witnesses by excluding their product

If every positive exclusion through `X^k` admits another witness through
`X`, the interval must contain more than `k` distinct witnesses.
-/

namespace Erdos478.EffectiveResolvent
open Finset

theorem count_of_avoidance {X k : ℕ} (hX : 0<X) (P : ℕ → Prop) [DecidablePred P]
    (positive : ∀ p, P p → 0<p)
    (avoid : ∀ C : ℕ, 0<C → C≤X^k → ∃ p≤X, P p ∧ ¬p ∣ C) :
    k < ((range (X+1)).filter P).card := by
  let F := (range (X+1)).filter P
  by_contra! h
  change F.card ≤ k at h
  have hC : 0 < ∏ p ∈ F, p := prod_pos (fun p hp => positive p (mem_filter.mp hp).2)
  have bound : (∏ p ∈ F, p) ≤ X^k := calc
    _ ≤ ∏ _p ∈ F, X := prod_le_prod' (fun p hp => by
      have := mem_range.mp (mem_filter.mp hp).1
      omega)
    _ = X^F.card := by simp
    _ ≤ X^k := Nat.pow_le_pow_right hX h
  obtain ⟨p,hp,hP,havoid⟩ := avoid _ hC bound
  exact havoid (dvd_prod_of_mem _ (mem_filter.mpr ⟨mem_range.mpr (by omega),hP⟩ : p ∈ F))

#print axioms count_of_avoidance

end Erdos478.EffectiveResolvent
