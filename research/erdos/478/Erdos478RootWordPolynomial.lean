import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic

/-!
# A polynomial encoding one root from each member of a family

A weighted resultant gives all sums of roots of two factors. Iteration
and Horner's rule give one root for each word of choices, over any field.
-/
namespace Erdos478.EffectiveResolvent
open Polynomial Finset

noncomputable def weightedSum {R : Type*} [CommRing R] (f g : R[X]) (M : R) (d e : ℕ) : R[X] :=
  (g.map (C : R →+* R[X])).resultant
    ((f.map C).comp (C X-C (C M)*X)) e d

theorem map_weightedSum {R K : Type*} [CommRing R] [CommRing K]
    (φ : R →+* K) (f g : R[X]) (M : R) (d e : ℕ) :
    (weightedSum f g M d e).map φ = weightedSum (f.map φ) (g.map φ) (φ M) d e := by
  let ψ := Polynomial.mapRingHom φ
  have hh : ψ.comp (C : R →+* R[X]) = (C : K →+* K[X]).comp φ := by ext a; simp [ψ]
  change ψ _ = _
  unfold weightedSum
  rw [← resultant_map_map,Polynomial.map_comp]
  have hl (p : R[X]) : (p.map (C : R →+* R[X])).map ψ = (p.map φ).map C := by
    simp only [Polynomial.map_map,hh]
  have ht : (C X-C (C M)*X : R[X][X]).map ψ = C X-C (C (φ M))*X := by
    simp [ψ]
  rw [hl,hl,ht]

theorem weightedSum_factors {K I J : Type*} [Field K] [Fintype I] [Fintype J]
    (a : I → K) (b : J → K) (M : K) :
    weightedSum (∏ i, (X-C (a i))) (∏ j, (X-C (b j))) M (Fintype.card I) (Fintype.card J) =
      ∏ j, ∏ i, (X-C (a i+M*b j)) := by
  let G : K[X][X] := ((∏ i, (X-C (a i)) : K[X]).map C).comp (C X-C (C M)*X)
  have hg : G.natDegree ≤ Fintype.card I := by
    have hl : (C (X : K[X])-C (C M)*X).natDegree ≤ 1 := by
      apply (natDegree_sub_le ..).trans (max_le (by simp) ?_)
      exact (natDegree_mul_le ..).trans (by simp)
    apply natDegree_comp_le.trans
    calc
      _ ≤ ((∏ i, (X-C (a i)) : K[X]).natDegree)*1 :=
        Nat.mul_le_mul natDegree_map_le hl
      _ = _ := by simp
  change ((∏ j, (X-C (b j)) : K[X]).map C).resultant G _ _ = _
  have hmapped : (∏ j, (X-C (b j)) : K[X]).map C = ∏ j, (X-C (C (b j)) : K[X][X]) := by
    simp only [Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C]
  rw [hmapped]
  let v (j : J) := (X-C (C (b j)) : K[X][X])
  have hd : (∏ j, v j).natDegree = Fintype.card J := by simp [v]
  change (∏ j, v j).resultant G (Fintype.card J) _ = _
  rw [← hd,resultant_prod_left _ _ _ _ (by simp [v]) hg]
  apply prod_congr rfl
  intro j _
  simp only [v,natDegree_X_sub_C,resultant_X_sub_C_left G _ _ hg,G,eval_comp,eval_sub,eval_C,eval_mul,eval_X]
  simp only [Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,eval_prod,eval_sub,eval_C,eval_X]
  apply prod_congr rfl
  intro i _
  simp only [map_add,map_mul]
  ring

abbrev Word {n : ℕ} (d : Fin n → ℕ) := (i : Fin n) → Fin (d i)

noncomputable def wordValue {K : Type*} [CommRing K] {n : ℕ} (M : K) (v : Fin n → K) :=
  ∑ i, M^i.val * v i

private theorem word_succ {K : Type*} [CommRing K] {n : ℕ} (M : K) (v : Fin (n+1) → K) :
    wordValue M v = v 0 + M*wordValue M (Fin.tail v) := by
  rw [wordValue,Fin.sum_univ_succ,wordValue,Finset.mul_sum]
  simp only [Fin.val_zero,pow_zero,one_mul,Fin.val_succ,Fin.tail]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [pow_succ]; ring

/-- One factor for each tuple choosing one root from each input polynomial. -/
noncomputable def wordPolynomial {R : Type*} [CommRing R] :
    (n : ℕ) → (Fin n → R[X]) → (Fin n → ℕ) → R → R[X]
  | 0, _, _, _ => X
  | n+1, f, d, M => weightedSum (f 0) (wordPolynomial n (Fin.tail f) (Fin.tail d) M)
      M (d 0) (∏ i : Fin n, d i.succ)

theorem wordPolynomial_map {R K : Type*} [CommRing R] [CommRing K] (φ : R →+* K)
    {n : ℕ} (f : Fin n → R[X]) (d : Fin n → ℕ) (M : R) :
    (wordPolynomial n f d M).map φ = wordPolynomial n (fun i => (f i).map φ) d (φ M) := by
  induction n with
  | zero => simp [wordPolynomial]
  | succ n ih =>
    rw [wordPolynomial,map_weightedSum,ih,wordPolynomial]
    rfl

theorem wordPolynomial_factors {K : Type*} [Field K] {n : ℕ} (d : Fin n → ℕ)
    (a : (i : Fin n) → Fin (d i) → K) (M : K) :
    wordPolynomial n (fun i => ∏ j, (X-C (a i j))) d M =
      ∏ t : Word d, (X-C (wordValue M (fun i => a i (t i)))) := by
  classical
  induction n with
  | zero => simp [wordPolynomial,wordValue,Word]
  | succ n ih =>
    let b (t : Word (Fin.tail d)) := wordValue M (fun i => a i.succ (t i))
    have he := ih (Fin.tail d) (fun i => a i.succ)
    change weightedSum _ (wordPolynomial n _ (Fin.tail d) M) M _ _ = _
    rw [show wordPolynomial n (Fin.tail (fun i => ∏ j, (X-C (a i j)))) (Fin.tail d) M =
      ∏ t : Word (Fin.tail d), (X-C (b t)) from he]
    have hc : Fintype.card (Word (Fin.tail d)) = ∏ i : Fin n, d i.succ := by
      change Fintype.card ((i : Fin n) → Fin (d i.succ)) = _
      simpa only [Fintype.card_fin] using (Fintype.card_pi (α := fun i : Fin n => Fin (d i.succ)))
    rw [← hc,← Fintype.card_fin (d 0),weightedSum_factors (a 0) b M,Finset.prod_comm]
    let e := Fin.consEquiv (fun i => Fin (d i))
    rw [← Fintype.prod_prod_type (fun p : Fin (d 0) × Word (Fin.tail d) =>
      (X-C (a 0 p.1 + M*b p.2)))]
    apply Fintype.prod_equiv e
    intro ⟨j,t⟩
    rw [word_succ]
    rfl


#print axioms map_weightedSum
#print axioms wordPolynomial_factors
#print axioms wordPolynomial_map

end Erdos478.EffectiveResolvent
