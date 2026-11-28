import CunninghamSquareGapRigidity

/-! Eventual irreducibility for both balanced Jones chains, including square coefficients. -/

namespace CunninghamChain.GapLift
open Polynomial Filter LinearRoots LargeGap

/-- For every a≥2 and either sign, the rational iterates from a(X−1) are
eventually irreducible. For square a the minus case uses two-degree comparison. -/
theorem balanced_eventually_irreducible {a : ℕ} (ha : 2 ≤ a) (k : Bool) :
    ∀ᶠ n : ℕ in atTop, Irreducible (term k a (-a) n) := by
  by_cases ok : k=true ∨ ¬ IsSquare a
  · filter_upwards [eventually_ge_atTop (gapThreshold (gapEndpoint a k)),eventually_gt_atTop 0]
      with n large hn
    exact eventual_balanced_iterate_of_gap ha k ok hn (by omega)
  have hk : k=false := by cases k <;> simp_all
  subst k
  have sq : IsSquare a := by simpa using ok
  obtain ⟨b,rfl⟩ := sq.exists_sq
  have hb : 2 ≤ b := by
    by_contra! small
    interval_cases b <;> norm_num at ha
  filter_upwards [eventual_square_rigidity hb,eventually_gt_atTop 0] with n rigid hn
  exact balanced_iterate_of_rigidity ha false hn rigid

/-- A single starting index works simultaneously for the plus and minus recurrences. -/
theorem both_balanced_eventually {a : ℕ} (ha : 2 ≤ a) :
    ∃ N : ℕ, ∀ n ≥ N, Irreducible (term true a (-a) n) ∧ Irreducible (term false a (-a) n) :=
  eventually_atTop.mp ((balanced_eventually_irreducible ha true).and (balanced_eventually_irreducible ha false))

#print axioms balanced_eventually_irreducible
#print axioms both_balanced_eventually

end CunninghamChain.GapLift
