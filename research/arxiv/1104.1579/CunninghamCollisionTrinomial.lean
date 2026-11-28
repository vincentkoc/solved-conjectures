import CunninghamPolynomialLengths

/-! The noncyclotomic cofactor of the collision trinomial of two opposite Jones iterates. -/

namespace CunninghamChain.SharedFactors
open Polynomial

noncomputable def geom (g s : ℕ) : ℤ[X] := ∑ i ∈ Finset.range s, (X^g)^i

/-- The reciprocal of the noncyclotomic part of Xⁿ+Xᵐ−2 for
m=gi and n=g(i+j), when i and j are coprime. -/
noncomputable def cofactor (g i j : ℕ) : ℤ[X] :=
  geom g (i+j) + X^(g*j)*geom g i

private lemma geom_identity (g s : ℕ) :
    (X^g-1)*geom g s = (X^(g*s)-1 : ℤ[X]) := by
  rw [geom,mul_comm,geom_sum_mul,←pow_mul]

lemma cofactor_identity (g i j : ℕ) :
    (X^g-1)*cofactor g i j = C 2*X^(g*(i+j)) - (X^(g*j)+1 : ℤ[X]) := by
  rw [cofactor,mul_add,mul_left_comm (X^g-1) (X^(g*j)),geom_identity,geom_identity]
  rw [Nat.mul_add,pow_add,show C (2:ℤ)=(2:ℤ[X]) by norm_num]
  ring

lemma cofactor_zero {g i j : ℕ} (hg : 0 < g) (hi : 0 < i) (hj : 0 < j) :
    (cofactor g i j).coeff 0 = 1 := by
  have h := congrArg (fun P : ℤ[X] => P.eval 0) (cofactor_identity g i j)
  simpa [←coeff_zero_eq_eval_zero, mul_coeff_zero, coeff_X_pow, hg.ne',hi.ne',hj.ne',
    show i+j ≠ 0 by omega] using h

private lemma trinomial_top {n r : ℕ} (hr : r<n) :
    let F : ℤ[X] := C 2*X^n-(X^r+1)
    F.natDegree = n ∧ F.leadingCoeff = 2 := by
  dsimp only
  have hs : (X^r+1 : ℤ[X]).natDegree ≤ r :=
    (natDegree_add_le ..).trans (by simp)
  have hd : (X^r+1 : ℤ[X]).degree < (C 2*X^n : ℤ[X]).degree := by
    rw [degree_C_mul_X_pow _ (by decide : (2:ℤ) ≠ 0)]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hs.trans_lt hr)
  rw [natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt hd),leadingCoeff_sub_of_degree_lt hd]
  simp only [natDegree_C_mul_X_pow n 2 (by decide : (2:ℤ) ≠ 0),leadingCoeff_mul,leadingCoeff_C,
    leadingCoeff_X_pow,mul_one,and_self]

lemma cofactor_shape {g i j : ℕ} (hg : 0 < g) (hi : 0 < i) :
    (cofactor g i j).natDegree+g = g*(i+j) ∧ (cofactor g i j).leadingCoeff=2 := by
  have hlt : g*j < g*(i+j) := Nat.mul_lt_mul_of_pos_left (by omega) hg
  obtain ⟨hd,hl⟩ := trinomial_top hlt
  rw [←cofactor_identity] at hd hl
  rw [leadingCoeff_mul,leadingCoeff_X_pow_sub_one hg,one_mul] at hl
  have hc : cofactor g i j ≠ 0 := by intro h; simp [h] at hl
  have hx : (X^g-1 : ℤ[X]) ≠ 0 := by
    intro h
    have := leadingCoeff_X_pow_sub_one (R := ℤ) hg
    simp [h] at this
  rw [natDegree_mul hx hc,show (X^g-1:ℤ[X]).natDegree = g from natDegree_X_pow_sub_C (r := 1)] at hd
  exact ⟨by omega,hl⟩

#print axioms cofactor_identity
#print axioms cofactor_zero
#print axioms cofactor_shape

end CunninghamChain.SharedFactors
