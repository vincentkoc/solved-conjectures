import CunninghamEffectiveSquareComparison
import CunninghamBalancedEndpointWeight
import CunninghamSquareGapRigidity

/-! Explicit finite-prefix criteria for both signs and every balanced coefficient. -/

namespace CunninghamChain.GapLift
open Polynomial CoefficientEnergy LinearRoots LargeGap

/-- A square coefficient on the minus side admits a cutoff exponential in its
endpoint weight, even though that quadratic endpoint factors. -/
theorem square_minus_of_explicit_weight {b n : ℕ} (hb : 2≤b)
    (large : 6*(3^(balancedWeight (b^2) false)+1) < n+2) :
    Irreducible (term false (b^2) (-(b^2:ℕ)) n) := by
  have ha : 2≤b^2 := by nlinarith
  have base : 0 < 3^(balancedWeight (b^2) false) := pow_pos (by decide) _
  have hn : 0 < n := by omega
  apply balanced_iterate_of_rigidity ha false hn
  apply square_rigidity_of_no_exception hb hn
  · rw [balanced_endpoint_degree ha]; omega
  · rw [balanced_endpoint_weight ha]
    rintro ⟨t,cap,exc⟩
    have deg := square_exception_degree_bound (b:=(b:ℚ)) (by exact_mod_cast (show 1<b by omega)) exc
    have mono := Nat.pow_le_pow_right (by decide : 0<3) cap
    omega

/-- The same closed bound works for all a≥2 and both signs. -/
theorem balanced_of_explicit_cutoff {a n : ℕ} (ha : 2 ≤ a) (k : Bool)
    (large : 12*4^(balancedWeight a true) ≤ n) : Irreducible (term k a (-a) n) := by
  have pos : 0<4^(balancedWeight a true) := pow_pos (by decide) _
  have hn : 0<n := by omega
  have weightLe : balancedWeight a k ≤ balancedWeight a true := by
    cases k with
    | true => rfl
    | false =>
      simp only [balancedWeight,Bool.false_eq_true,if_false,if_true]
      gcongr
      omega
  by_cases ok : k=true ∨ ¬IsSquare a
  · apply eventual_balanced_iterate_of_gap ha k ok hn
    rw [gapThreshold_eq ha]
    have le := Nat.pow_le_pow_right (by decide : 0<4) weightLe
    omega
  have hk : k=false := by cases k <;> simp_all
  subst k
  obtain ⟨b,rfl⟩ := (show IsSquare a by simpa using ok).exists_sq
  have hb : 2≤b := by by_contra! small; interval_cases b <;> norm_num at ha
  apply square_minus_of_explicit_weight hb
  have le₁ : 3^(balancedWeight (b^2) false) ≤ 4^(balancedWeight (b^2) false) :=
    Nat.pow_le_pow_left (by decide) _
  have le₂ := Nat.pow_le_pow_right (by decide : 0<4) weightLe
  omega

/-- The infinite simultaneous test for a balanced seed is equivalent to its explicit
finite prefix, without a squarefreeness or nonsquare hypothesis. -/
theorem both_balanced_iff_explicit_prefix {a : ℕ} (ha : 2≤a) :
    (∀ (k : Bool) (n : ℕ), Irreducible (term k a (-a) n)) ↔
      ∀ (k : Bool) (n : ℕ), n < 12*4^(1+5*a^2+(a+1)^2) → Irreducible (term k a (-a) n) := by
  constructor
  · exact fun h k n _ => h k n
  intro h k n
  by_cases small : n < 12*4^(1+5*a^2+(a+1)^2)
  · exact h k n small
  · exact balanced_of_explicit_cutoff ha k (by simpa only [balancedWeight,if_true] using Nat.le_of_not_gt small)

#print axioms square_minus_of_explicit_weight
#print axioms balanced_of_explicit_cutoff
#print axioms both_balanced_iff_explicit_prefix

end CunninghamChain.GapLift
