import Erdos478JointRootBound
import Erdos478TwoOrbitFactors
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-! # The separating two-letter polynomial of a doubly transitive input -/

namespace Erdos478.PrimeDifferences
open Polynomial Finset EffectiveResolvent UniqueFactorizationMonoid
open scoped Polynomial
noncomputable section

def pairWord (f : ℤ[X]) (n M : ℕ) : ℤ[X] :=
  wordPolynomial 2 (fun _ => f) (fun _ => n) (M:ℤ)

/-- A bounded integer separates every ordered pair. The resulting polynomial
is separable and has exactly two rational irreducible factors. -/
theorem pair_word_two {K : Type*} [Field K] [NumberField K] [Normal ℚ K]
    (f : ℤ[X]) {n : ℕ} (hn : 2≤n) (v : Fin n ↪ K)
    (hf : f.map (Int.castRingHom K)=∏ i, (X-C (v i)))
    (closed : ∀ (σ : K ≃ₐ[ℚ] K) i, ∃ j, σ (v i)=v j)
    (conj : ∀ i j a b, i≠j → a≠b → ∃ σ : K ≃ₐ[ℚ] K, σ (v i)=v a ∧ σ (v j)=v b) :
    ∃ M : ℕ, (pairWord f n M).Monic ∧ 0<(pairWord f n M).natDegree ∧
      ((pairWord f n M).map (Int.castRingHom ℚ)).Separable ∧
      (normalizedFactors ((pairWord f n M).map (Int.castRingHom ℚ))).card=2 := by
  classical
  let d (_ : Fin 2) := n
  obtain ⟨M,_,hinj⟩ := word_separator (by decide : 0<2) d (fun _ => v)
  let t (q : Word d) := wordValue (M:K) (fun i => v (q i))
  have ht (q : Word d) : t q=v (q 0)+(M:K)*v (q 1) := by simp [t,wordValue,Fin.sum_univ_two]
  let W := pairWord f n M
  let Q := W.map (Int.castRingHom ℚ)
  have lift : Q.map (algebraMap ℚ K)=W.map (Int.castRingHom K) := by
    dsimp only [Q]
    rw [Polynomial.map_map,RingHom.ext_int ((algebraMap ℚ K).comp _) (Int.castRingHom K)]
  have fac : W.map (Int.castRingHom K)=∏ q : Word d, (X-C (t q)) := by
    unfold W pairWord
    rw [wordPolynomial_map]
    simp_rw [hf]
    simpa [d,t] using wordPolynomial_factors d (fun _ i => v i) (M:K)
  have mon : W.Monic := (Function.Injective.monic_map_iff (f:=Int.castRingHom K)
    (by exact Int.cast_injective)).mpr (fac ▸ monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _))
  have sep : Q.Separable := (separable_map (algebraMap ℚ K)).mp (lift.trans fac ▸ separable_prod_X_sub_C_iff.mpr hinj)
  have sp : (Q.map (algebraMap ℚ K)).Splits := lift.trans fac ▸ Splits.prod fun _ _ => Splits.X_sub_C _
  have root (x : K) : aeval x Q=0 ↔ ∃ a b, x=v a+(M:K)*v b := by
    rw [← eval_map_algebraMap,lift,fac,eval_prod,Finset.prod_eq_zero_iff]
    simp only [mem_univ,true_and,eval_sub,eval_X,eval_C,sub_eq_zero,ht]
    exact ⟨fun ⟨q,hq⟩ => ⟨q 0,q 1,hq⟩,fun ⟨a,b,h⟩ => ⟨![a,b],by simpa using h⟩⟩
  have pairinj : Function.Injective (fun q : Fin n × Fin n => v q.1+(M:K)*v q.2) := by
    rintro ⟨a,b⟩ ⟨c,e⟩ h
    have eq : (![a,b] : Fin 2 → Fin n)=![c,e] := hinj (show t ![a,b]=t ![c,e] by simpa only [ht,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using h)
    exact Prod.ext (congrFun eq 0) (congrFun eq 1)
  let i : Fin n := ⟨0,by omega⟩
  let j : Fin n := ⟨1,by omega⟩
  have hfac := pair_factors v M i j (by simp [i,j]) closed conj pairinj (mon.map _) sep sp root
  have integ (x : K) : IsIntegral ℚ x := .of_finite ℚ x
  have : Nonempty (Word d) := ⟨fun _ => i⟩
  refine ⟨M,mon,?_,sep,?_⟩
  · rw [← mon.natDegree_map (Int.castRingHom K),fac]
    simpa using (Fintype.card_pos (α:=Word d))
  · change (normalizedFactors (W.map (Int.castRingHom ℚ))).card=2
    rw [hfac,normalizedFactors_mul (minpoly.ne_zero (integ _)) (minpoly.ne_zero (integ _)),
      normalizedFactors_irreducible (minpoly.irreducible (integ _)),normalizedFactors_irreducible (minpoly.irreducible (integ _))]
    rfl

#print axioms pair_word_two
end
end Erdos478.PrimeDifferences
