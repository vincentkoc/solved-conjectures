import Mathlib

/-! Degree restrictions for coprime polynomial factors of an almost perfect power. -/

namespace CunninghamChain
open Polynomial
open scoped Polynomial

variable {K : Type*} [Field K]

private lemma degree_of_coprime_power {A B H : K[X]} {N : ℕ} (ha : A≠0)
    (hc : IsCoprime A B) (he : A*B=H^N) : N ∣ A.natDegree := by
  obtain ⟨D,hD⟩ := exists_associated_pow_of_mul_eq_pow' hc he
  have hD₀ : D^N≠0 := by
    rintro hz
    have := hD.dvd
    rw [hz,zero_dvd_iff] at this
    exact ha this
  have hdeg := le_antisymm (natDegree_le_of_dvd hD.symm.dvd hD₀) (natDegree_le_of_dvd hD.dvd ha)
  exact ⟨D.natDegree,hdeg.trans (natDegree_pow ..)⟩

private lemma degrees_with_X {A B H : K[X]} {N : ℕ} (ha : A≠0) (hb : B≠0)
    (hc : IsCoprime A B) (he : (X-1)*(A*B)=X*H^N) (hx : X ∣ A) :
    (N ∣ A.natDegree ∧ N ∣ B.natDegree) ∨
    (N ∣ A.natDegree-1 ∧ N ∣ B.natDegree+1) := by
  obtain ⟨U,rfl⟩ := hx
  have hu : U≠0 := right_ne_zero_of_mul ha
  have hc' := hc.of_mul_left_right
  have hX : (X-1:K[X]) ≠ 0 := by simpa using (X_sub_C_ne_zero (1:K))
  have hI : Irreducible (X-1:K[X]) := by simpa using (irreducible_X_sub_C (1:K))
  have hU : ((X-1)*U)*B=H^N := by
    apply mul_left_cancel₀ (X_ne_zero : (X:K[X])≠0)
    linear_combination he
  have hxdeg : (X*U).natDegree=U.natDegree+1 := by rw [natDegree_mul X_ne_zero hu,natDegree_X,Nat.add_comm]
  have hleft (T : K[X]) (ht : T≠0) : ((X-1)*T).natDegree=T.natDegree+1 := by
    rw [natDegree_mul hX ht,show (X-1:K[X]).natDegree=1 by simpa using natDegree_X_sub_C (1:K),Nat.add_comm]
  by_cases hd : X-1 ∣ B
  · have hf : ¬X-1 ∣ U := fun h => hI.not_isUnit (hc'.isUnit_of_dvd' h hd)
    have cop := (hI.coprime_iff_not_dvd.mpr hf).symm.mul_right hc'
    have eqn : U*((X-1)*B)=H^N := by linear_combination hU
    have d₁ := degree_of_coprime_power hu cop eqn
    have d₂ := degree_of_coprime_power (mul_ne_zero hX hb) cop.symm (show ((X-1)*B)*U=H^N by rwa [mul_comm])
    right
    simpa [hxdeg,hleft B hb] using And.intro d₁ d₂
  · have cop := (hI.coprime_iff_not_dvd.mpr hd).mul_left hc'
    have d₁ := degree_of_coprime_power (mul_ne_zero hX hu) cop hU
    have d₂ := degree_of_coprime_power hb cop.symm (show B*((X-1)*U)=H^N by rwa [mul_comm])
    left
    simpa [hxdeg,hleft U hu] using And.intro d₁ d₂

/-- A coprime splitting of (X−1)AB = XHᴺ has either two degree multiples of N
or one degree on each side of a multiple of N. -/
theorem factor_degrees_of_shifted_power {A B H : K[X]} {N : ℕ} (ha : A≠0) (hb : B≠0)
    (hc : IsCoprime A B) (he : (X-1)*(A*B)=X*H^N) :
    (N ∣ A.natDegree ∧ N ∣ B.natDegree) ∨
    (N ∣ A.natDegree-1 ∧ N ∣ B.natDegree+1) ∨
    (N ∣ A.natDegree+1 ∧ N ∣ B.natDegree-1) := by
  have hx : (X:K[X]) ∣ (X-1)*(A*B) := he ▸ dvd_mul_right ..
  have h₁ : ¬(X:K[X]) ∣ X-1 := by simp [X_dvd_iff]
  rcases prime_X.dvd_mul.mp ((prime_X.dvd_mul.mp hx).resolve_left h₁) with h|h
  · rcases degrees_with_X ha hb hc he h with h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases degrees_with_X hb ha hc.symm (show (X-1)*(B*A)=X*H^N by rwa [mul_comm B A]) h with h|h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h.symm)

/-- If (X−1)AB is a power and A,B are coprime, at least one factor degree is
divisible by its exponent. -/
theorem factor_degree_of_linear_times_product {A B H : K[X]} {N : ℕ} (ha : A≠0) (hb : B≠0)
    (hc : IsCoprime A B) (he : (X-1)*(A*B)=H^N) : N ∣ A.natDegree ∨ N ∣ B.natDegree := by
  have hI : Irreducible (X-1:K[X]) := by simpa using irreducible_X_sub_C (1:K)
  by_cases h : X-1 ∣ A
  · have hB : ¬X-1 ∣ B := fun hB => hI.not_isUnit (hc.isUnit_of_dvd' h hB)
    exact Or.inr (degree_of_coprime_power hb ((hI.coprime_iff_not_dvd.mpr hB).mul_left hc).symm
      (show B*((X-1)*A)=H^N by linear_combination he))
  · exact Or.inl (degree_of_coprime_power ha ((hI.coprime_iff_not_dvd.mpr h).symm.mul_right hc)
      (show A*((X-1)*B)=H^N by linear_combination he))

#print axioms factor_degree_of_linear_times_product
#print axioms factor_degrees_of_shifted_power

end CunninghamChain
