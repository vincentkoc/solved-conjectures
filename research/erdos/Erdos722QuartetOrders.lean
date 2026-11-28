import Mathlib.Tactic

/-!
# Orders in the four-point block construction

The replication number is the order of an auxiliary pairwise balanced design.
Truncating one group of a five-group transversal design gives orders 4t+u.
-/

namespace Erdos722.QuartetOrders

def admissible (n : ℕ) : Prop := n % 4 = 0 ∨ n % 4 = 1

def transversalOrders : Finset ℕ := {4,5,8,9,13,16,17,20,25,29,32,37,41,49,53}

def baseExceptions : Finset ℕ := {13,28,29,48,49}

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem finite_cover : ∀ n : Fin 240, 12 < n.val → (n.val % 4 = 0 ∨ n.val % 4 = 1) →
    n.val ∈ baseExceptions ∨ ∃ t ∈ transversalOrders, 4*t ≤ n.val ∧ n.val ≤ 5*t := by decide

/-- Every admissible replication number above twelve either has one of five explicit
base orders or comes from truncating a smaller five-group transversal design. -/
theorem decompose {n : ℕ} (hn : 12 < n) (h : admissible n) :
    n ∈ baseExceptions ∨ ∃ t u : ℕ, n = 4*t+u ∧ u ≤ t ∧ t < n ∧ u < n ∧
      admissible t ∧ admissible u ∧ (t ∈ transversalOrders ∨ t % 12 = 1) := by
  have pack (t : ℕ) (ht : admissible t) (hl : 4*t ≤ n) (hu : n ≤ 5*t)
      (hc : t ∈ transversalOrders ∨ t%12=1) : ∃ t u : ℕ, n = 4*t+u ∧ u ≤ t ∧ t < n ∧ u < n ∧
        admissible t ∧ admissible u ∧ (t ∈ transversalOrders ∨ t%12=1) := by
    refine ⟨t,n-4*t,by omega,by omega,by omega,by omega,ht,?_,hc⟩
    unfold admissible at h ⊢
    omega
  by_cases hb : n < 240
  · obtain he | ⟨t,hT,hl,hu⟩ := finite_cover ⟨n,hb⟩ hn h
    · exact Or.inl he
    · have hvalid : ∀ t ∈ transversalOrders, t%4=0 ∨ t%4=1 := by decide
      exact Or.inr (pack t (hvalid _ hT) hl hu (Or.inl hT))
  · let t := 12*((n-4)/48)+1
    apply Or.inr (pack t ?_ ?_ ?_ ?_)
    · dsimp [admissible,t]; omega
    · dsimp [t]; omega
    · dsimp [t]; omega
    · right; dsimp [t]; omega

#print axioms decompose

end Erdos722.QuartetOrders
