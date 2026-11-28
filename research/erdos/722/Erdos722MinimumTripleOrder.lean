import Erdos722SteinerOrderGap
import Erdos722ProjectiveSublines
import Erdos722BinaryQuadruples
import Mathlib.Algebra.IsPrimePow

/-!
# Minimum nontrivial orders of Steiner 3-designs

Witt's sublines on a projective line over the quadratic extension attain
the strengthened lower bound for all the indicated prime-power block sizes.
-/

namespace Erdos722.MinimumOrder

/-- Orders strictly larger than one block, in the same predicate as Erdős 722. -/
def orders (r k : ℕ) : Set ℕ := {v | k < v ∧
  ∃ H : Finset (Finset (Fin v)), H.IsBlockDesign r k}

/-- Except for the three specified prime powers, the quadratic subline
construction has the least possible order among all nontrivial designs. -/
theorem prime_power_minimum {Q : ℕ} (hQ : IsPrimePow Q) (h₃ : 3 < Q)
    (h₅ : Q ≠ 5) (h₁₁ : Q ≠ 11) : IsLeast (orders 3 (Q+1)) (Q^2+1) := by
  constructor
  · refine ⟨by nlinarith [Nat.mul_le_mul_left Q (by omega : 2≤Q)],?_⟩
    obtain ⟨p,a,hp,ha,rfl⟩ := (isPrimePow_nat_iff _).mp hQ
    let : Fact p.Prime := ⟨hp⟩
    exact Sublines.exists_prime_power_subline_design p a 2 ha (by decide)
  · rintro v ⟨hv,H,hH⟩
    simpa using triple_square_lower (by omega : 3<Q+1) hv (by omega) (by omega) (by omega) hH

/-- The binary affine design attains the first admissible order at block size four. -/
theorem four_minimum : IsLeast (orders 3 4) 8 := by
  refine ⟨⟨by decide,exists_binary_quadruple_design 3⟩,?_⟩
  rintro v ⟨hv,H,hH⟩
  have h := boundary_or_square (by decide : 3≤3) (by decide : 3<4) hv hH
  norm_num at h
  omega

#print axioms prime_power_minimum
#print axioms four_minimum
end Erdos722.MinimumOrder
