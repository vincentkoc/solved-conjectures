import FormalConjecturesUtil
import Mathlib.Tactic

/-! # The higher block sizes passing the rank-three binomial tests through order fifty -/

namespace Erdos722.SmallOrders

/-- The eleven arithmetically admissible pairs above block size four. -/
def higherParameters (k n : ℕ) : Prop :=
  (k=5 ∧ (n=17 ∨ n=26 ∨ n=41 ∨ n=50)) ∨
  (k=6 ∧ (n=22 ∨ n=26 ∨ n=42 ∨ n=46)) ∨
  (k=7 ∧ (n=22 ∨ n=37)) ∨ (k=8 ∧ n=50)

private theorem parameter_table :
    ∀ k n : Fin 51, 4 < k.val → k.val < n.val →
      ((((k.val-2) ∣ n.val-2) ∧
       (k.val-1).choose 2 ∣ (n.val-1).choose 2 ∧ k.val.choose 3 ∣ n.val.choose 3) ↔
      higherParameters k.val n.val) := by
  unfold higherParameters
  decide

/-- Exact enumeration with the subtractions and binomial coefficients used upstream. -/
theorem higher_admissible_iff {k n : ℕ} (hk : 4<k) (hkn : k<n) (hn : n≤50) :
    (∀ i<3, (k-i).choose (3-i) ∣ (n-i).choose (3-i)) ↔ higherParameters k n := by
  have h := parameter_table ⟨k,by omega⟩ ⟨n,by omega⟩ hk hkn
  constructor
  · intro hc
    exact h.mp ⟨by simpa using hc 2 (by decide),by simpa using hc 1 (by decide),by simpa using hc 0 (by decide)⟩
  · intro hp i hi
    obtain ⟨h₂,h₁,h₀⟩ := h.mpr hp
    interval_cases i
    · simpa using h₀
    · simpa using h₁
    · simpa using h₂

#print axioms higherParameters
#print axioms higher_admissible_iff
end Erdos722.SmallOrders
