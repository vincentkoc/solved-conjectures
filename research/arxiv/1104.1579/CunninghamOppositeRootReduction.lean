import CunninghamRepeatedRootIndices

/-! Elimination of the seed and the four possible reduced index pairs. -/

namespace CunninghamChain.SharedFactors
open Polynomial LinearRoots

/-- A complex number which is not a root of unity of any positive order. -/
def OffUnity (z : ℂ) : Prop := ∀ d : ℕ, 0 < d → z^d ≠ 1

private lemma collision_eq {a b : ℤ} {m s : ℕ} {k : Bool} {z : ℂ} (hu : OffUnity z)
    (hm : aeval z (term k a b m) = 0) (hn : aeval z (term (!k) a b (m+s)) = 0) :
    2*z^(m+s) = z^s+1 := by
  have h1 : z ≠ 1 := by simpa using hu 1 (by decide)
  have e := (root_equation k a b m z h1).mp hm
  have f := (root_equation (!k) a b (m+s) z h1).mp hn
  rw [pow_add] at f ⊢
  cases k
  · norm_num [sign] at e f
    linear_combination f - z^s*e
  · norm_num [sign] at e f
    linear_combination z^s*e - f

private lemma integral_divisibility {a b : ℤ} {g i j : ℕ} (hg : 0 < g) (hi : 0 < i)
    (hj : 0 < j) (hcop : Nat.Coprime i j) {k : Bool} {z : ℂ} (hu : OffUnity z)
    (hm : aeval z (term k a b (g*i)) = 0)
    (hn : aeval z (term (!k) a b (g*i+g*j)) = 0) :
    cofactor g i j ∣ polynomialTerm k (C a*X+C b) (g*i) ∧
      aeval z ((cofactor g i j).map (Int.castRingHom ℚ)) = 0 := by
  have eq := collision_eq hu hm hn
  rw [←Nat.mul_add] at eq
  let Q := cofactor g i j
  have hq : aeval z (Q.map (Int.castRingHom ℚ)) = 0 := by
    have e := congrArg (fun P : ℤ[X] => aeval z (P.map (Int.castRingHom ℚ))) (cofactor_identity g i j)
    have he : (z^g-1)*aeval z (Q.map (Int.castRingHom ℚ)) = 0 := by
      have h2 : aeval z (2 : ℚ[X]) = 2 := map_ofNat _ _
      simpa [Q,Polynomial.map_sub,h2,eq] using e
    exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr (hu g hg))
  have prim : Q.IsPrimitive := isPrimitive_iff_isUnit_of_C_dvd.mpr fun r h =>
    isUnit_of_dvd_unit ((C_dvd_iff_dvd_coeff _ _).mp h 0) (by
      dsimp [Q]; rw [cofactor_zero hg hi hj]; exact isUnit_one)
  refine ⟨?_,hq⟩
  apply (IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast Q _ prim).mpr
  exact ((cofactor_irreducible hg hi hj hcop).dvd_iff_aeval_eq_zero hq).mp hm

/-- Every off-unity opposite-sign collision has an integral cofactor divisor at the earlier
index. The only possible (g,i,j) are (1,1,1), (1,1,2), (1,2,1), (2,1,1). -/
theorem reduced_collision {a b : ℤ} (ha : a ≠ 0) {m s : ℕ} (hm : 0 < m) (hs : 0 < s)
    {k : Bool} {z : ℂ} (hu : OffUnity z) (hmz : aeval z (term k a b m) = 0)
    (hnz : aeval z (term (!k) a b (m+s)) = 0) :
    ∃ g i j : ℕ, m=g*i ∧ s=g*j ∧
      (∃ u v : ℤ, polynomialTerm k (C a*X+C b) m = cofactor g i j * (C u*X+C v)) ∧
      aeval z ((cofactor g i j).map (Int.castRingHom ℚ)) = 0 ∧
      ((g=1 ∧ i=1 ∧ j=1) ∨ (g=1 ∧ i=1 ∧ j=2) ∨
       (g=1 ∧ i=2 ∧ j=1) ∨ (g=2 ∧ i=1 ∧ j=1)) := by
  obtain ⟨g,i,j,hg,hcop,hi',hj'⟩ := Nat.exists_coprime' (Nat.gcd_pos_of_pos_left s hm)
  rw [mul_comm i] at hi'
  rw [mul_comm j] at hj'
  have hi : 0 < i := Nat.pos_of_mul_pos_left (hi' ▸ hm)
  have hj : 0 < j := Nat.pos_of_mul_pos_left (hj' ▸ hs)
  subst m s
  obtain ⟨div,hroot⟩ := integral_divisibility hg hi hj hcop hu hmz hnz
  obtain ⟨hb,hgap⟩ := collision_index_bounds ha hg hi hj div
  have hg2 := (Nat.le_mul_of_pos_right g hi).trans hb
  have hi2 := (Nat.le_mul_of_pos_left i hg).trans hb
  have hj3 := (Nat.le_mul_of_pos_left j hg).trans hgap
  obtain ⟨B,hB⟩ := div
  have hD := quotient_degree ha hg hi hB
  have := Nat.le_mul_of_pos_right g hj
  obtain ⟨u,v,hlin⟩ := exists_eq_X_add_C_of_natDegree_le_one (show B.natDegree ≤ 1 by omega)
  refine ⟨g,i,j,rfl,rfl,⟨u,v,by rwa [hlin] at hB⟩,hroot,?_⟩
  interval_cases g <;> interval_cases i <;> interval_cases j <;> norm_num at *

#print axioms reduced_collision

end CunninghamChain.SharedFactors
