import CunninghamSquareGapEisenstein
import CunninghamTwoDegreeLift

/-! The four endpoint terms in a two-degree comparison of square balanced seeds. -/

namespace CunninghamChain.GapLift
open Polynomial Finset

variable {ι : Type*} [Fintype ι]

def positions (n : ℕ) (x : ι → ℕ) : ι ⊕ Fin 4 → ℕ := Sum.elim x ![0,n+2,n+1,n]
def witness (a : ι → ℚ) : ι ⊕ Fin 4 → ℚ := Sum.elim a (fun _ => 0)
def endpoint (u : ℚ) : ι ⊕ Fin 4 → ℚ := Sum.elim (fun _ => 0) ![1,u,-2*u,u-1]

noncomputable def tailPoly (u : ℚ) (n : ℕ) : ℚ[X] := X^n*(C u*(X-1)^2-1)

private lemma tail_as_sum (u : ℚ) (n : ℕ) : monomial (n+2) u+
    monomial (n+1) (-2*u)+monomial n (u-1)=tailPoly u n := by
  simp only [tailPoly,←C_mul_X_pow_eq_monomial,pow_succ,map_sub,map_mul,map_neg,map_ofNat,map_one]
  ring

theorem lift_endpoint (u : ℚ) {n m : ℕ} (le : n ≤ m) (x y : ι → ℕ) :
    liftTerms (m+2) (positions n x) (positions m y) (endpoint u) =
      (X : (ℚ[X])[X])^(n+2)*(X^(m-n)+C (tailPoly u n)) := by
  have h₁ : m+2+(n+2)-(m+2)=n+2 := by omega
  have h₂ : m+2+(n+1)-(m+1)=n+2 := by omega
  have h₃ : m+2+n-m=n+2 := by omega
  simp only [liftTerms,positions,endpoint,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    map_zero,sum_const_zero,zero_add,Fin.sum_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.tail_cons,Matrix.head_cons,h₁,h₂,h₃,Nat.add_zero,Nat.sub_zero]
  rw [show m+2=(n+2)+(m-n) by omega,←tail_as_sum]
  simp only [← C_mul_X_pow_eq_monomial,map_add,map_one,pow_zero,mul_one,one_mul,pow_add,pow_succ]
  ring

/-- Any two configurations with the same equality pattern on differences
force divisibility at the first degree, after specializing the lifted variable at one. -/
theorem square_comparison {b : ℚ} (hb : 1 < b) {n m : ℕ} (lt : n < m) (x y : ι → ℕ)
    (hx : ∀ i, x i ≤ n+2) (hy : ∀ i, y i ≤ m+2)
    (same : ∀ i j k l, positions n x i+(n+2-positions n x j)=positions n x k+(n+2-positions n x l) →
      positions m y i+(m+2-positions m y j)=positions m y k+(m+2-positions m y l))
    (a : ι → ℚ)
    (prod : assemble (positions n x) (witness a)*assemble (fun i => n+2-positions n x i) (witness a) =
      assemble (positions n x) (endpoint (b^2))*assemble (fun i => n+2-positions n x i) (endpoint (b^2))) :
    (1+tailPoly (b^2) n) ∣ assemble (positions n x) (witness a) ∨
    (1+tailPoly (b^2) n) ∣ assemble (fun i => n+2-positions n x i) (witness a) := by
  have bounded (v : ℕ) (z : ι → ℕ) (hz : ∀ i, z i ≤ v+2) (i : ι ⊕ Fin 4) :
      positions v z i ≤ v+2 := by
    cases i with
    | inl i => exact hz i
    | inr j => fin_cases j <;> simp [positions]
  let E := (X : (ℚ[X])[X])^(m-n)+C (tailPoly (b^2) n)
  have prime : Prime E := (square_endpoint_binomial hb n (d:=m-n) (by omega)).prime
  have lift := lift_product_eq _ _ (bounded n x hx) (bounded m y hy) same _ _ prod
  have de : E ∣ liftTerms (m+2) (positions n x) (positions m y) (witness a) *
      liftTerms (m+2) (fun i => n+2-positions n x i) (fun i => m+2-positions m y i) (witness a) := by
    rw [lift,lift_endpoint _ lt.le]
    exact (dvd_mul_left E _).trans (dvd_mul_right ..)
  rcases prime.dvd_mul.mp de with h|h
  · left
    simpa [E,eval_one_lift] using map_dvd (evalRingHom (1:ℚ[X])) h
  · right
    simpa [E,eval_one_lift] using map_dvd (evalRingHom (1:ℚ[X])) h

#print axioms lift_endpoint
#print axioms square_comparison

end CunninghamChain.GapLift
