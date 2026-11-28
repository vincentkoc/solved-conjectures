import Mathlib.GroupTheory.Perm.Centralizer

/-!
# Permutations commuting with a pairing

A fixed-point-free involution of a set of size (2r) has (r) cycles of
length two. Its centralizer permutes those pairs and may interchange the
two members of each pair.
-/

namespace Erdos478.SplittingDensity

/-- There are exactly `2^r * r!` permutations preserving the pairing. -/
theorem card_pairing_centralizer {α : Type*} [Fintype α] {r : ℕ}
    (g : Equiv.Perm α) (hg : g ^ 2 = 1) (hfix : ∀ a, g a ≠ a)
    (hc : Fintype.card α = 2*r) :
    Nat.card (Subgroup.centralizer {g}) = 2^r * r.factorial := by
  classical
  have hsup : g.support = Finset.univ := by
    ext a
    simp [Equiv.Perm.mem_support,hfix]
  have htype := Equiv.Perm.cycleType_of_pow_prime_eq_one hg
  have hsum := g.sum_cycleType
  rw [hsup,Finset.card_univ,hc] at hsum
  have hnum : g.cycleType.card = r := by
    calc
      g.cycleType.card = g.cycleType.sum / 2 := by
        conv_rhs => rw [htype,Multiset.sum_replicate]
        simp
      _ = r := by rw [hsum]; omega
  rw [hnum] at htype
  rw [Equiv.Perm.nat_card_centralizer,hsum,hc,Nat.sub_self,htype]
  by_cases hr : r = 0
  · simp [hr]
  · simp [Multiset.prod_replicate,Multiset.toFinset_replicate,hr]

#print axioms card_pairing_centralizer
end Erdos478.SplittingDensity
