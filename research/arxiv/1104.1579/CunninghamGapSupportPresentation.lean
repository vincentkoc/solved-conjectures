import CunninghamGapPatternFiniteness
import CunninghamEventualBalancedIrreducibility

/-! Relating the two-degree configurations to the integer Jones iterates. -/

namespace CunninghamChain.GapLift
open Polynomial Finset CoefficientEnergy LinearRoots LargeGap

lemma support_card_le_energy (G : ℤ[X]) {N : ℕ} (dg : G.natDegree ≤ N) :
    (G.support.card:ℤ) ≤ energy G (N+1) := by
  calc
    _ = ∑ _i ∈ G.support, (1:ℤ) := by simp
    _ ≤ ∑ i ∈ G.support, (G.coeff i)^2 := by
      apply sum_le_sum
      intro i hi
      have nz := mem_support_iff.mp hi
      have := sq_pos_of_ne_zero nz
      omega
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro i hi
        exact mem_range.mpr (by have := (le_natDegree_of_mem_supp i hi).trans dg; omega)
      · intros; positivity

lemma assemble_support (G : ℤ[X]) (N : ℕ) (dg : G.natDegree ≤ N) :
    ∃ (x : Fin G.support.card → ℕ) (a : Fin G.support.card → ℚ),
      (∀ i, x i ≤ N) ∧ assemble x a=G.map (Int.castRingHom ℚ) := by
  classical
  let e := G.support.equivFin.symm
  let x (i : Fin G.support.card) : ℕ := (e i).val
  let a (i : Fin G.support.card) := (G.coeff (x i):ℚ)
  refine ⟨x,a,fun i => (le_natDegree_of_mem_supp _ (e i).property).trans dg,?_⟩
  have orig : (∑ i ∈ G.support, monomial i (G.coeff i))=G := G.sum_monomial_eq
  have cast := congrArg (Polynomial.map (Int.castRingHom ℚ)) orig
  rw [Polynomial.map_sum] at cast
  simp only [map_monomial] at cast
  unfold assemble
  rw [←cast]
  exact (e.sum_comp (fun j : G.support => monomial j.val (G.coeff j.val:ℚ))).trans
    (by simpa only [Finset.univ_eq_attach,Int.coe_castRingHom] using
      Finset.sum_attach G.support (fun i => monomial i (G.coeff i:ℚ)))

lemma reflect_assemble {ι : Type*} [Fintype ι] (N : ℕ) (x : ι → ℕ) (a : ι → ℚ)
    (hx : ∀ i, x i ≤ N) :
    reflect N (assemble x a)=assemble (fun i => N-x i) a := by
  let H : ℚ[X] →+ ℚ[X] := ⟨⟨reflect N,reflect_zero⟩,fun p q => reflect_add p q N⟩
  change H (∑ i, monomial (x i) (a i))=_
  rw [map_sum]
  apply sum_congr rfl
  intro i _
  change reflect N (monomial (x i) (a i))=_
  rw [←C_mul_X_pow_eq_monomial,reflect_C_mul_X_pow,revAt_le (hx i),C_mul_X_pow_eq_monomial]

lemma present_witness {ι : Type*} [Fintype ι] (n : ℕ) (x : ι → ℕ) (a : ι → ℚ) :
    assemble (positions n x) (witness a)=assemble x a := by
  simp [assemble,positions,witness,Fintype.sum_sum_type]

lemma present_endpoint {ι : Type*} [Fintype ι] (n : ℕ) (x : ι → ℕ) (u : ℚ) :
    assemble (positions n x) (endpoint u)=1+tailPoly u n := by
  have h := congrArg (Polynomial.eval (1:ℚ[X])) (lift_endpoint u (n:=n) le_rfl x x)
  simpa only [eval_one_lift,eval_mul,eval_X,eval_add,eval_pow,one_pow,one_mul,eval_C] using h

lemma integral_endpoint (a n : ℕ) :
    (separated (gapEndpoint a false) (n+2)).map (Int.castRingHom ℚ)=1+tailPoly a n := by
  have ep : gapEndpoint a false=monomial 0 (a:ℤ)+monomial 1 (-2*(a:ℤ))+monomial 2 ((a:ℤ)-1) := by
    simp [gapEndpoint,gapQuadratic,sign,←C_mul_X_pow_eq_monomial]
    ring
  have term (i : ℕ) (h : i ≤ n+2) (c : ℤ) :
      reflect (n+2) (monomial i c)=monomial (n+2-i) c := by
    rw [←C_mul_X_pow_eq_monomial,reflect_C_mul_X_pow,revAt_le h,C_mul_X_pow_eq_monomial]
  rw [separated,ep,reflect_add,reflect_add,term 0 (by omega),term 1 (by omega),term 2 (by omega)]
  simp only [Polynomial.map_add,Polynomial.map_one,map_monomial,Nat.sub_zero,Nat.add_sub_cancel,
    show n+2-1=n+1 by omega,Int.coe_castRingHom,Int.cast_natCast,Int.cast_mul,Int.cast_neg,Int.cast_ofNat,
    Int.cast_sub,Int.cast_one]
  simp only [tailPoly,←C_mul_X_pow_eq_monomial,pow_succ,map_sub,map_mul,map_neg,map_ofNat,map_one]
  ring

#print axioms support_card_le_energy
#print axioms assemble_support
#print axioms integral_endpoint

end CunninghamChain.GapLift
