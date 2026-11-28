import Erdos478ResolventSeparator
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# A permutation resolvent over the integers

Symmetric coefficients give a single integral polynomial whose factorization
over any splitting field records the weighted sums for all orderings of the
roots. This permits comparison across characteristics.
-/

namespace Erdos478.EffectiveResolvent
open Finset Polynomial
open scoped Polynomial

private abbrev Vars (n : ℕ) := MvPolynomial (Fin n) ℤ

private noncomputable def linearTag (n M : ℕ) (σ : Equiv.Perm (Fin n)) : Vars n :=
  ∑ i : Fin n, MvPolynomial.C (M^i.val : ℤ) * MvPolynomial.X (σ i)

private noncomputable def generic (n M : ℕ) : (Vars n)[X] :=
  ∏ σ : Equiv.Perm (Fin n), (X-C (linearTag n M σ))

private theorem rename_tag (n M : ℕ) (π σ : Equiv.Perm (Fin n)) :
    MvPolynomial.rename π (linearTag n M σ) = linearTag n M (π*σ) := by
  simp [linearTag,Equiv.Perm.mul_apply]

private theorem symmetric_coeff (n M j : ℕ) : ((generic n M).coeff j).IsSymmetric := by
  intro π
  change (MvPolynomial.rename π).toRingHom ((generic n M).coeff j) = _
  rw [← Polynomial.coeff_map]
  congr 1
  unfold generic
  have hr (σ : Equiv.Perm (Fin n)) : (MvPolynomial.rename π).toRingHom (linearTag n M σ) =
      linearTag n M (π*σ) := rename_tag n M π σ
  simp only [Polynomial.map_prod,Polynomial.map_sub,map_X,map_C,hr]
  exact Equiv.prod_comp (Equiv.mulLeft π) (fun σ => (X-C (linearTag n M σ)))

private noncomputable def expression (n M j : ℕ) : Vars n :=
  (MvPolynomial.esymmAlgEquiv (Fin n) ℤ (Fintype.card_fin n)).symm ⟨_,symmetric_coeff n M j⟩

private theorem express (n M j : ℕ) :
    MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℤ (i.val+1)) (expression n M j) =
      (generic n M).coeff j := by
  rw [← MvPolynomial.esymmAlgHom_apply]
  exact congrArg Subtype.val ((MvPolynomial.esymmAlgEquiv (Fin n) ℤ (Fintype.card_fin n)).apply_symm_apply _)

private def signedCoeff (n : ℕ) (f : ℤ[X]) (i : Fin n) : ℤ :=
  (-1)^(i.val+1)*f.coeff (n-(i.val+1))

/-- The integral resolvent recording all weighted sums of ordered roots. -/
noncomputable def resolvent (n M : ℕ) (f : ℤ[X]) : ℤ[X] := by
  classical
  exact Polynomial.ofFn (n.factorial+1) fun j =>
    MvPolynomial.eval (signedCoeff n f) (expression n M j.val)

private theorem height_generic (n M : ℕ) : (generic n M).natDegree ≤ n.factorial := by
  classical
  unfold generic
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin n), (X-C (linearTag n M σ)).natDegree :=
      natDegree_prod_le univ (fun σ : Equiv.Perm (Fin n) => X-C (linearTag n M σ))
    _ = n.factorial := by simp [Fintype.card_perm]

private theorem specialise_expression {K : Type*} [Field K] (a : Fin n → K) (f : ℤ[X])
    (hw : ∀ i : Fin n, ((signedCoeff n f i : ℤ) : K) =
      MvPolynomial.aeval a (MvPolynomial.esymm (Fin n) ℤ (i.val+1))) (M j : ℕ) :
    (MvPolynomial.eval (signedCoeff n f) (expression n M j) : ℤ) =
      (MvPolynomial.aeval a ((generic n M).coeff j) : K) := by
  rw [← express]
  let h₁ : Vars n →+* K := (Int.castRingHom K).comp (MvPolynomial.eval (signedCoeff n f))
  let h₂ : Vars n →+* K := (MvPolynomial.aeval a).toRingHom.comp
    (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℤ (i.val+1))).toRingHom
  change h₁ _ = h₂ _
  have h : h₁ = h₂ := by
    ext i <;> simp [h₁,h₂,hw]
  rw [h]

private theorem evaluated_generic {K : Type*} [Field K] (a : Fin n → K) (M : ℕ) :
    (generic n M).map (MvPolynomial.aeval a).toRingHom =
    ∏ σ : Equiv.Perm (Fin n), (X-C (tag a σ (M:K))) := by
  classical
  simp only [generic,Polynomial.map_prod,Polynomial.map_sub,map_X,map_C]
  apply prod_congr rfl
  intro σ _
  congr 2
  change MvPolynomial.aeval a (linearTag n M σ) = _
  simp [linearTag,tag,Polynomial.ofFn_eq_sum_monomial,Polynomial.eval_finsetSum,mul_comm]

private theorem elementary_specializes {K : Type*} [Field K] (a : Fin n → K) (f : ℤ[X])
    (h : f.map (Int.castRingHom K) = ∏ i, (X-C (a i))) (i : Fin n) :
    ((signedCoeff n f i : ℤ) : K) = MvPolynomial.aeval a (MvPolynomial.esymm (Fin n) ℤ (i.val+1)) := by
  classical
  let s := univ.val.map a
  have hcard : s.card = n := by simp [s]
  have hroots : (s.map (fun t => X-C t)).prod = f.map (Int.castRingHom K) := by
    rw [h]
    simp [s,Finset.prod,Function.comp_def]
  have hv := s.prod_X_sub_C_coeff (k := n-(i.val+1)) (by omega)
  rw [hroots,coeff_map,hcard,show n-(n-(i.val+1)) = i.val+1 by omega] at hv
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
  unfold signedCoeff
  push_cast
  change (Int.castRingHom K) (f.coeff _) = _ at hv
  change _ * (Int.castRingHom K) (f.coeff _) = _
  rw [hv,← mul_assoc,← mul_pow]
  simp [s]

/-- In any field where the input polynomial factors into the indicated
linear factors, the same integer resolvent records all permuted root sums. -/
theorem resolvent_factors {K : Type*} [Field K] (a : Fin n → K) (f : ℤ[X])
    (h : f.map (Int.castRingHom K) = ∏ i, (X-C (a i))) (M : ℕ) :
    (resolvent n M f).map (Int.castRingHom K) =
      ∏ σ : Equiv.Perm (Fin n), (X-C (tag a σ (M:K))) := by
  classical
  rw [← evaluated_generic]
  ext j
  simp only [coeff_map]
  by_cases hj : j<n.factorial+1
  · simpa [resolvent,Polynomial.ofFn_coeff_eq_val_of_lt _ hj] using
      specialise_expression a f (elementary_specializes a f h) M j
  · have hgen : (generic n M).coeff j = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (height_generic ..) (by omega))
    simp [resolvent,hgen,Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega : n.factorial+1 ≤ j)]

private theorem map_tag {K : Type*} [Field K] (φ : K →+* K) (a : Fin n → K) (M : ℕ)
    (σ : Equiv.Perm (Fin n)) : φ (tag a σ (M:K)) = tag (φ ∘ a) σ (M:K) := by
  classical
  simp [tag,Polynomial.ofFn_eq_sum_monomial,Polynomial.eval_finsetSum,Function.comp_def]

/-- An endomorphism permuting the roots and fixing one separating weighted
sum fixes each root individually. -/
theorem fixed_of_tag {K : Type*} [Field K] (φ : K →+* K) (a : Fin n ↪ K) (M : ℕ)
    (hs : Function.Injective (fun σ => tag a σ (M:K)))
    (hp : ∀ i, ∃ j, φ (a i) = a j) (τ : Equiv.Perm (Fin n))
    (ht : φ (tag a τ (M:K)) = tag a τ (M:K)) : ∀ i, φ (a i) = a i := by
  classical
  choose idx hi using hp
  have hj : Function.Injective idx := fun i j he =>
    a.injective (φ.injective ((hi i).trans ((congrArg a he).trans (hi j).symm)))
  let π := Equiv.ofBijective idx ((Finite.injective_iff_bijective).mp hj)
  have he : φ ∘ a = a ∘ π := funext hi
  rw [map_tag,he] at ht
  have hh : π*τ = τ := hs ht
  intro i
  have equ : π i = i := by
    have e := DFunLike.congr_fun hh (τ.symm i)
    simpa [Equiv.Perm.mul_apply] using e
  exact (hi i).trans (congrArg a equ)

#print axioms fixed_of_tag
#print axioms resolvent_factors

end Erdos478.EffectiveResolvent
