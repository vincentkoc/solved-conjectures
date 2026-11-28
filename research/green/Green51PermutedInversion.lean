import Green51PermutedTopFlats

/-! # Inversion supplies a permutation with no constant derivative -/
open Finset Polynomial Green50Downsets
open scoped Classical
namespace Green51PermutedPairs
theorem inverse_not_constant {K:Type*} [Field K] [Fintype K] [CharP K 2]
    (big:4<Fintype.card K) {t:K} (tn:t≠0) :
    ¬∀ x:K,x⁻¹+(x+t)⁻¹=(0:K)⁻¹+t⁻¹ := by
  intro h
  classical
  let P:K[X]:=X^2+C t*X+C (t^2)
  have dlow : (C t*X+C (t^2)).natDegree<2 := by
    apply lt_of_le_of_lt (natDegree_add_le _ _)
    simp [tn]
  have degree:P.natDegree=2 := by
    change (X^2+C t*X+C (t^2)).natDegree=2
    rw [add_assoc,natDegree_add_eq_left_of_natDegree_lt (by simpa using dlow),natDegree_X_pow]
  have pn:P≠0 := by intro z;rw [z,natDegree_zero] at degree;omega
  have sub:((univ:Finset K).erase 0).erase t ⊆ P.roots.toFinset := by
    intro x hx
    obtain ⟨xt,hx⟩:=mem_erase.mp hx
    have xn: x≠0 := (mem_erase.mp hx).1
    have plus:x+t≠0 := by
      intro e
      have e': -x=t := neg_eq_iff_add_eq_zero.mpr e
      rw [←CharTwo.neg_eq x] at xt
      exact xt e'
    have r:=h x
    rw [inv_zero,zero_add] at r
    field_simp [xn,tn,plus] at r
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots pn).mpr
    change eval x P=0
    simp only [P,eval_add,eval_pow,eval_X,eval_mul,eval_C]
    have two:(2:K)=0 := CharP.cast_eq_zero K 2
    rw [add_right_comm x t x,←two_mul,two,zero_mul,zero_add] at r
    calc
      _ = x*(x+t)+t*t := by ring
      _ = t*t+t*t := by rw [←r]
      _ = 0 := by rw [←two_mul,two,zero_mul]
  have count:=(card_le_card sub).trans (P.roots.toFinset_card_le.trans (card_roots' _))
  rw [degree,card_erase_of_mem (mem_erase.mpr ⟨tn,mem_univ _⟩),card_erase_of_mem (mem_univ _),card_univ] at count
  omega
/-- Inversion in a finite binary field produces a permutation with no nonzero constant derivative. -/
theorem exists_no_constant_derivative (n:ℕ) (large:3≤n) :
    ∃ f : Cube n ≃ Cube n,¬∃ t:Cube n,t≠0 ∧ ∀x:Cube n,f x+f (x+t)=f 0+f t := by
  classical
  let K:=GaloisField 2 n
  let : Fintype K := Fintype.ofFinite K
  let e : Cube n ≃ₗ[ZMod 2] K := LinearEquiv.ofFinrankEq _ _ (by
    rw [show Module.finrank (ZMod 2) K=n from GaloisField.finrank 2 (by omega)]
    simp [Cube])
  let f:=e.toEquiv.trans ((Equiv.inv K).trans e.symm.toEquiv)
  refine ⟨f,?_⟩
  rintro ⟨t,tn,const⟩
  have sz:Fintype.card K=2^n := by rw [←Nat.card_eq_fintype_card];exact GaloisField.card 2 n (by omega)
  have lim:=Nat.pow_le_pow_right (by decide : 0<2) large
  apply inverse_not_constant (K:=K) (by omega) (t:=e t) (fun h=>tn (e.injective (h.trans e.map_zero.symm)))
  intro y
  have h:=congrArg e (const (e.symm y))
  have fval (z:Cube n) : e (f z)=(e z)⁻¹ := e.apply_symm_apply _
  simpa only [map_add,fval,e.apply_symm_apply,e.map_zero] using h

end Green51PermutedPairs

#print axioms Green51PermutedPairs.inverse_not_constant
#print axioms Green51PermutedPairs.exists_no_constant_derivative
