import Green51PencilWindows

/-! # Coefficients of a product of odd Frobenius conjugates -/

open Polynomial Finset
namespace Green51PencilWindows
open FiniteField
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]

noncomputable def sigma : K ≃ₐ[F] K := (frobeniusAlgEquivOfAlgebraic F K)^2

noncomputable def orbit (b : K) (i : ℕ) := (sigma^i) (b^2)

omit [CharP K 2] in
theorem orbit_expr (b : K) (i : ℕ) : orbit b i = b^(2^(2*i+1)) := by
  dsimp only [orbit,sigma]
  rw [←pow_mul,AlgEquiv.coe_pow,coe_frobeniusAlgEquivOfAlgebraic_iterate,ZMod.card]
  change (b^2)^(2^(2*i))=b^(2^(2*i+1))
  rw [←pow_mul]
  congr 1
  rw [pow_succ,mul_comm]

/-- The product over the first `k` odd Frobenius conjugates of the ratio `b`. -/
noncomputable def companion (k : ℕ) (b : K) := window k (orbit b) 0
noncomputable def term (k : ℕ) (b : K) (i : ℕ) := (companion k b).coeff (k-i)

omit [CharP K 2] in
theorem term_zero (k : ℕ) (b : K) : term k b 0=1 := by
  let P:=companion k b
  have monicP : P.Monic := by
    dsimp only [P,companion,window]
    exact monic_prod_of_monic _ _ (fun h _ => monic_X_sub_C (orbit b (0+h)))
  have degP : P.natDegree=k := by
    dsimp only [P,companion,window]
    rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
    simp
  change P.coeff (k-0)=1
  rw [Nat.sub_zero,←degP]
  exact monicP

omit [CharP K 2] in
private theorem sigma_four (z : K) : sigma.toRingHom z = z^4 := by
  change (sigma (K:=K)) z = z^4
  rw [sigma,AlgEquiv.coe_pow,coe_frobeniusAlgEquivOfAlgebraic_iterate,ZMod.card]
  rfl

omit [CharP K 2] in
private theorem companion_identity {k : ℕ} (degK : Module.finrank F K = 2*k+1) (b : K) :
    (X-C (b^2))*(companion k b).map sigma.toRingHom = (X-C b)*companion k b := by
  let P:=companion k b
  have last : orbit b k=b := by
    have cardK := Module.card_eq_pow_finrank (K:=F) (V:=K)
    rw [ZMod.card,degK] at cardK
    rw [orbit_expr,←cardK,pow_card]
  have eq := slide k (orbit b) 0
  simp only [zero_add,orbit, pow_zero,AlgEquiv.one_apply] at eq
  have moved := map_window (sigma (K:=K)) (b^2) k 1
  simp only [pow_one] at moved
  change P.map sigma.toRingHom = window k (orbit b) 1 at moved
  change (X-C (b^2))*window k (orbit b) 1 = (X-C (orbit b k))*P at eq
  rw [←moved,last] at eq
  exact eq

theorem term_step {k : ℕ} (degK : Module.finrank F K=2*k+1) (b : K) (i : ℕ) (hi : i<k) :
    (term k b (i+1))^4 + term k b (i+1) = b^2*(term k b i)^4+b*term k b i := by
  let P := companion k b
  have eq := companion_identity degK b
  have cf:=congrArg (fun S : K[X] => S.coeff (k-(i+1)+1)) eq
  simp only [coeff_X_sub_C_mul,coeff_map] at cf
  simp only [sigma_four,show k-(i+1)+1=k-i by omega] at cf
  change (P.coeff (k-(i+1)))^4 + P.coeff (k-(i+1)) = b^2*(P.coeff (k-i))^4+b*P.coeff (k-i)
  dsimp only [P]
  linear_combination (norm := (ring_nf;reduce_mod_char!)) cf

theorem term_end {k : ℕ} (degree : Module.finrank F K=2*k+1) (b : K) :
    b^2*(term k b k)^4+b*(term k b k)=0 := by
  have eq:=congrArg (fun P : K[X] => P.coeff 0) (companion_identity degree b)
  simp only [sub_mul,coeff_sub,coeff_X_mul_zero,coeff_C_mul,coeff_map,sigma_four] at eq
  simp only [term,Nat.sub_self]
  linear_combination (norm := (ring_nf; reduce_mod_char!)) -eq

/-- If the coefficient ratio generates the field, the shifted factors used by
the pencil are all distinct. -/
theorem orbit_distinct {k : ℕ} (degree : Module.finrank F K = 2*k+1) {b : K}
    (generates : Algebra.adjoin F {b} = ⊤) :
    Set.InjOn (orbit b) (Set.Iio (2*k)) := by
  have ord := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F K
  have cop : (orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic F K)).Coprime 2 := by
    rw [ord,degree,Nat.coprime_comm,Nat.prime_two.coprime_iff_not_dvd]
    omega
  have ord' : orderOf (sigma (K:=K))=2*k+1 := cop.orderOf_pow.trans (ord.trans degree)
  intro i hi j hj eq
  have same : ((sigma (K:=K))^i) b = (sigma^j) b := by
    apply (frobeniusEquiv K 2).injective
    change (((sigma (K:=K))^i) b)^2 = ((sigma^j) b)^2
    simpa only [orbit,map_pow] using eq
  have maps : ((sigma (K:=K))^i).toAlgHom=((sigma^j).toAlgHom) :=
    AlgHom.ext_of_adjoin_eq_top generates (by rintro x (rfl : x=b);exact same)
  have equals : ((sigma (K:=K))^i) = sigma^j := by
    ext z
    exact DFunLike.congr_fun maps z
  apply pow_injOn_Iio_orderOf _ _ equals
  · change i < orderOf (sigma (K:=K));change i<2*k at hi;omega
  · change j < orderOf (sigma (K:=K));change j<2*k at hj;omega

theorem term_independent {k : ℕ} (degree : Module.finrank F K=2*k+1) {b : K}
    (generates : Algebra.adjoin F {b}=⊤) :
    LinearIndependent F (fun j : Fin (k+1) => term k b j.val) := by
  have h := coefficients_independent (sigma (K:=K)) (b^2) k (orbit_distinct degree generates)
  convert h.comp Fin.rev Fin.rev_injective using 1
  funext j
  change (companion k b).coeff (k-j.val) = (companion k b).coeff j.rev.val
  congr 1
  simp [Fin.rev]

omit [CharP K 2] in
theorem term_map {E : Type*} [Field E] [Algebra F E] [Fintype E]
    (j : E →ₐ[F] K) (b : E) (k i : ℕ) : term k (j b) i = j (term k b i) := by
  have eq : (companion k b).map j.toRingHom = companion k (j b) := by
    simp only [companion,window,Polynomial.map_prod]
    apply Finset.prod_congr rfl
    intro x _
    rw [Polynomial.map_sub,map_X,map_C,orbit_expr,orbit_expr]
    simp
  rw [term,←eq,coeff_map]
  rfl

end Green51PencilWindows

#print axioms Green51PencilWindows.orbit_expr
#print axioms Green51PencilWindows.term_zero
#print axioms Green51PencilWindows.term_step
#print axioms Green51PencilWindows.term_end
#print axioms Green51PencilWindows.orbit_distinct
#print axioms Green51PencilWindows.term_independent
#print axioms Green51PencilWindows.term_map
