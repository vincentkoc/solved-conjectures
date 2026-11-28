import Mathlib

/-! Coefficient-square bounds for a polynomial and for a reflected integral factor. -/

namespace CunninghamChain.CoefficientEnergy
open Polynomial

/-- Sum of the squares of coefficients below N, excluding the coefficient at N. -/
def energy (P : ℤ[X]) (N : ℕ) : ℤ := ∑ i ∈ Finset.range N, (P.coeff i)^2

lemma energy_stable (P : ℤ[X]) {N M : ℕ} (hd : P.natDegree<N) (h : N≤M) :
    energy P M = energy P N := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le h
  unfold energy
  rw [Finset.sum_range_add]
  rw [add_eq_left]
  apply Finset.sum_eq_zero
  intro i _
  simp [coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree<N+i)]

lemma energy_shift (P : ℤ[X]) (n N : ℕ) :
    energy (X^n*P) (n+N)=energy P N := by
  unfold energy
  rw [Finset.sum_range_add]
  have hz : ∑ i ∈ Finset.range n, ((X^n*P).coeff i)^2 = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [coeff_X_pow_mul',not_le.mpr (Finset.mem_range.mp hi)]
  rw [hz,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.add_comm n i,coeff_X_pow_mul]

lemma energy_scale (s : ℤ) (P : ℤ[X]) (N : ℕ) :
    energy (C s*P) N=s^2*energy P N := by
  simp [energy,mul_pow,Finset.mul_sum]

lemma energy_add (P Q : ℤ[X]) (N : ℕ) :
    energy (P+Q) N ≤ 2*energy P N+2*energy Q N := by
  simp only [energy,coeff_add,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [sq_nonneg (P.coeff i-Q.coeff i)]

lemma energy_sub (P Q : ℤ[X]) (N : ℕ) :
    energy (P-Q) N ≤ 2*energy P N+2*energy Q N := by
  simpa [sub_eq_add_neg,energy] using energy_add P (-Q) N

private lemma coeff_sq_le (P : ℤ[X]) {i N : ℕ} (hi : i<N) :
    (P.coeff i)^2 ≤ energy P N :=
  Finset.single_le_sum (f:=fun i => (P.coeff i)^2) (fun _ _ => sq_nonneg _) (Finset.mem_range.mpr hi)

/-- The middle coefficient is the full squared weight through degree N. -/
lemma coeff_mul_self_reflect (P : ℤ[X]) (N : ℕ) :
    (P*reflect N P).coeff N = energy P (N+1) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i k => P.coeff i * (reflect N P).coeff k)]
  unfold energy
  apply Finset.sum_congr rfl
  intro i hi
  rw [coeff_reflect,revAt_le (by omega : N-i≤N),Nat.sub_sub_self (by simpa using Finset.mem_range.mp hi)]
  ring

private lemma flip_energy (A B : ℤ[X]) (N : ℕ) (hN : N=A.natDegree+B.natDegree) :
    energy (A.reverse*B) (N+1)=energy (A*B) (N+1) := by
  subst N
  rw [←coeff_mul_self_reflect,←coeff_mul_self_reflect,reflect_mul _ _ A.reverse_natDegree_le le_rfl,reflect_mul _ _ le_rfl le_rfl]
  unfold reverse
  rw [reflect_reflect]
  ring

private lemma unit_sq {x : ℤ} (h : IsUnit x) : x^2=1 := by
  rcases Int.isUnit_iff.mp h with rfl|rfl <;> decide

/-- Once the lower coefficients carry less than one quarter of the leading
coefficient's squared magnitude, every factor with unit endpoints is reciprocal up to sign. -/
theorem reciprocal_of_small_tail (A B : ℤ[X]) (hB : B≠0)
    (hu : IsUnit A.leadingCoeff) (hv : IsUnit (A.coeff 0))
    (small : 4*energy (A*B) (A*B).natDegree < (A*B).leadingCoeff^2) :
    A = C (A.leadingCoeff*A.coeff 0)*A.reverse := by
  let s := A.leadingCoeff*A.coeff 0
  let P := A*B
  let J := C s*(A.reverse*B)
  have ha : A≠0 := leadingCoeff_ne_zero.mp hu.ne_zero
  have hs : s^2=1 := by rw [show s^2=A.leadingCoeff^2*(A.coeff 0)^2 by simp [s,mul_pow],unit_sq hu,unit_sq hv]; decide
  have hs0 : s≠0 := by intro h; simp [h] at hs
  have htr : A.natTrailingDegree=0 := natTrailingDegree_eq_zero.mpr (Or.inr hv.ne_zero)
  have hdR : A.reverse.natDegree=A.natDegree := by rw [reverse_natDegree,htr,Nat.sub_zero]
  have hlR : A.reverse.leadingCoeff=A.coeff 0 := by rw [reverse_leadingCoeff,trailingCoeff,htr]
  have np : P≠0 := mul_ne_zero ha hB
  have nR : A.reverse*B≠0 := mul_ne_zero (reverse_eq_zero.not.mpr ha) hB
  have nj : J≠0 := mul_ne_zero (C_ne_zero.mpr hs0) nR
  have dp : P.natDegree=A.natDegree+B.natDegree := natDegree_mul ha hB
  have dj : J.natDegree=P.natDegree := by simp only [J,natDegree_C_mul hs0,natDegree_mul (reverse_eq_zero.not.mpr ha) hB,hdR,dp]
  have lj : J.leadingCoeff=P.leadingCoeff := by
    simp only [J,P,leadingCoeff_mul,leadingCoeff_C,hlR,s]
    linear_combination A.leadingCoeff*B.leadingCoeff*(unit_sq hv)
  have full : energy J (P.natDegree+1)=energy P (P.natDegree+1) := by
    rw [show J=C s*(A.reverse*B) from rfl,energy_scale,hs,one_mul,flip_energy _ _ _ dp]
  have tail : energy J P.natDegree=energy P P.natDegree := by
    unfold energy at full ⊢
    rw [Finset.sum_range_succ,Finset.sum_range_succ] at full
    have eq : J.coeff P.natDegree=P.coeff P.natDegree := by
      rwa [←dj,←leadingCoeff,dj,←leadingCoeff]
    rw [eq] at full
    exact add_right_cancel full
  change A=C s*A.reverse
  by_contra neq
  let D := A-C s*A.reverse
  have nd : D≠0 := sub_ne_zero.mpr neq
  have net : P-J=D*B := by dsimp [P,J,D]; ring
  have nnet : P-J≠0 := net ▸ mul_ne_zero nd hB
  let i := (P-J).natDegree
  have di : i<P.natDegree := by
    have h := degree_sub_lt_left (p:=P) (q:=J)
      (by rw [degree_eq_natDegree np,degree_eq_natDegree nj,dj]) np lj.symm
    simpa [i,degree_eq_natDegree np,degree_eq_natDegree nnet] using h
  have h1 := coeff_sq_le P di
  have h2 := coeff_sq_le J di
  rw [tail] at h2
  have high : P.coeff i-J.coeff i=D.leadingCoeff*B.leadingCoeff := by
    rw [←coeff_sub]
    change (P-J).leadingCoeff=_
    rw [net,leadingCoeff_mul]
  have low : 1 ≤ D.leadingCoeff^2 := by
    have hh := leadingCoeff_ne_zero.mpr nd
    rcases lt_or_gt_of_ne hh with h|h <;> nlinarith
  have bound : B.leadingCoeff^2 ≤ (P.coeff i-J.coeff i)^2 := by
    rw [high,mul_pow]
    exact le_mul_of_one_le_left (sq_nonneg _) low
  change 4*energy P P.natDegree < (A*B).leadingCoeff^2 at small
  rw [leadingCoeff_mul,mul_pow,unit_sq hu,one_mul] at small
  nlinarith [sq_nonneg (P.coeff i+J.coeff i)]

#print axioms reciprocal_of_small_tail

end CunninghamChain.CoefficientEnergy
