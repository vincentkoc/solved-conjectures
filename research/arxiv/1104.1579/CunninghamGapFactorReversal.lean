import CunninghamLargeGapRigidity

/-! Factor reversal with the reciprocal linear multiplier of a Jones iterate. -/

namespace CunninghamChain.LargeGap
open Polynomial

/-- When an anti-reciprocal linear multiplier gives a rigid separated product,
every two-factor decomposition has a factor invariant up to signed reversal. -/
theorem factor_reversal_of_rigid (L A B c : ℤ[X]) {N : ℕ} (rigid : ∀ G : ℤ[X], G.natDegree≤N →
      G*reflect N G=separated c N*reflect N (separated c N) →
      ∃ s : ℤ, s^2=1 ∧ (G=C s*separated c N ∨ reflect N G=C s*separated c N))
    (lnz : L≠0) (anz : A≠0) (bnz : B≠0)
    (dl : L.natDegree≤1) (rl : reflect 1 L= -L)
    (size : N=1+(A.natDegree+B.natDegree)) (eq : separated c N=L*(A*B)) :
    ∃ s : ℤ, s^2=1 ∧ (A.reverse=C s*A ∨ B.reverse=C (-s)*B) := by
  let G := L*(A.reverse*B)
  have da : A.reverse.natDegree ≤ A.natDegree :=
    natDegree_reflect_le.trans (max_le le_rfl le_rfl)
  have dr : reflect A.natDegree A.reverse=A := reflect_reflect
  have drG : reflect N G= -L*(A*B.reverse) := by
    dsimp only [G]
    rw [size,reflect_mul _ _ dl (natDegree_mul_le.trans (Nat.add_le_add_right da _)),
      reflect_mul _ _ da le_rfl,rl,dr]
    rfl
  have drF : reflect N (separated c N)= -L*(A.reverse*B.reverse) := by
    rw [eq,size,reflect_mul _ _ dl natDegree_mul_le,reflect_mul _ _ le_rfl le_rfl,rl]
    rfl
  have dg : G.natDegree≤N := by
    rw [size]
    exact natDegree_mul_le.trans (Nat.add_le_add dl
      (natDegree_mul_le.trans (Nat.add_le_add_right da _)))
  have prod : G*reflect N G=separated c N*reflect N (separated c N) := by
    rw [drG,drF,eq]
    dsimp only [G]
    ring
  obtain ⟨s,hs,h|h⟩ := rigid G dg prod
  · refine ⟨s,hs,Or.inl ?_⟩
    apply mul_left_cancel₀ (mul_ne_zero lnz bnz)
    rw [eq] at h
    dsimp only [G] at h
    linear_combination h
  · refine ⟨s,hs,Or.inr ?_⟩
    apply mul_left_cancel₀ (mul_ne_zero lnz anz)
    rw [drG,eq] at h
    rw [map_neg]
    linear_combination -h

/-- The explicit large-gap bound supplies rigidity for every irreducible endpoint. -/
theorem factor_reversal (L A B c : ℤ[X]) {N : ℕ} (irr : Irreducible c)
    (large : gapThreshold c ≤ N) (lnz : L≠0) (anz : A≠0) (bnz : B≠0)
    (dl : L.natDegree≤1) (rl : reflect 1 L= -L)
    (size : N=1+(A.natDegree+B.natDegree)) (eq : separated c N=L*(A*B)) :
    ∃ s : ℤ, s^2=1 ∧ (A.reverse=C s*A ∨ B.reverse=C (-s)*B) := by
  exact factor_reversal_of_rigid L A B c (fun G => large_gap_rigidity G c irr large)
    lnz anz bnz dl rl size eq

#print axioms factor_reversal_of_rigid
#print axioms factor_reversal

end CunninghamChain.LargeGap
