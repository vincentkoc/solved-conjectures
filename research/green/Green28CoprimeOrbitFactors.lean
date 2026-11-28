import Green28PrimeOrbitIndex
import Green28PrimeFactors

/-! Identifying the factors of a uniform law from coprime root orders. -/

namespace Green28CoprimeOrbitFactors

open Finset Polynomial Green28PrimitiveSupport Green28PrimeOrbitIndex

/-- The constant term of a monic divisor belongs to the cyclic group generated
by the signed root. At small index, a divisor with constant term one is a
whole component or the empty product. -/
theorem divisor_constant {K : Type} [Field K] {p d n c : ℕ} [prime : Fact p.Prime]
    [CharP K p] [IsAlgClosed K] {H : ℤ[X]} (hm : H.Monic) (orbit : PrimeOrbit H p d n)
    (index : n*c = digitSum p (range d)) (small : c ≤ p)
    {u : K[X]} (um : u.Monic) (dvd : u ∣ H.map (Int.castRingHom K)) :
    (u.coeff 0)^n = 1 ∧ (u.coeff 0 = 1 → u = 1 ∨ u = H.map (Int.castRingHom K)) := by
  classical
  obtain ⟨v,hv⟩ := dvd
  have vm := um.of_mul_monic_left (hv ▸ hm.map (Int.castRingHom K))
  let _ := ZMod.algebra K p
  let emb : AlgebraicClosure (ZMod p) →ₐ[ZMod p] K := IsAlgClosed.lift
  obtain ⟨β,ord,fac⟩ := orbit
  have mapped := congrArg (Polynomial.map emb.toRingHom) fac
  simp only [Polynomial.map_map,Polynomial.map_prod,Polynomial.map_sub,map_X,map_C,
    RingHom.ext_int (emb.toRingHom.comp _) (Int.castRingHom K)] at mapped
  simp only [emb.toRingHom.map_neg,emb.toRingHom.map_pow] at mapped
  obtain ⟨U,sub,h⟩ := divisor_subproduct (fun i => -(emb β)^(p^i)) (range d) um vm (hv.symm.trans mapped)
  have constant : u.coeff 0 = (emb β)^digitSum p U := by
    rw [coeff_zero_eq_eval_zero,h,eval_prod]
    simp [digitSum,Finset.prod_pow_eq_pow_sum]
  have rootOrder : IsPrimitiveRoot (emb β) n := ord.map_of_injective emb.injective
  constructor
  · rw [constant,←pow_mul,Nat.mul_comm,pow_mul,rootOrder.pow_eq_one,one_pow]
  · intro unit
    by_cases empty : U = ∅
    · left; simpa only [empty,prod_empty] using h
    by_cases full : U = range d
    · right; rw [mapped,←full]; exact h
    have live := nonempty_iff_ne_empty.mpr empty
    obtain ⟨i,hi⟩ := nonempty_iff_ne_empty.mpr empty
    have hd := mem_range.mp (sub hi)
    exact False.elim (no_small_index_selection prime.out.one_lt (by omega) index small
      (lt_of_le_of_ne sub full) live (rootOrder.dvd_of_pow_eq_one _ (constant ▸ unit)))

/-- Elements of pairwise coprime torsion orders cannot cancel across a product. -/
theorem constants_of_coprime_orders {ι K : Type*} [DecidableEq ι] [CommMonoid K]
    (S : Finset ι) (a : ι → K) (n : ι → ℕ) (torsion : ∀ i ∈ S, (a i)^(n i) = 1)
    (cop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (n i).Coprime (n j))
    (unit : ∏ i ∈ S, a i = 1) : ∀ i ∈ S, a i = 1 := by
  intro i hi
  let T := S.erase i
  let m := ∏ j ∈ T, n j
  have hcop : (n i).Coprime m := Nat.Coprime.prod_right (fun j hj =>
    cop i hi j (mem_erase.mp hj).2 (mem_erase.mp hj).1.symm)
  have pow1 : (∏ j ∈ T, a j)^m = 1 := by
    rw [←Finset.prod_pow]
    apply Finset.prod_eq_one
    intro j hj
    obtain ⟨q,hq⟩ := Finset.dvd_prod_of_mem n hj
    rw [show m = n j*q from hq,pow_mul,torsion j (mem_erase.mp hj).2,one_pow]
  have eq : a i * (∏ j ∈ T, a j) = 1 := (mul_prod_erase S a hi).trans unit
  have pow2 := congrArg (fun x:K => x^m) eq
  rw [mul_pow,pow1,mul_one,one_pow] at pow2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd
    (orderOf_dvd_of_pow_eq_one (torsion i hi)) (orderOf_dvd_of_pow_eq_one pow2)))

/-- Split a monic divisor of a finite product into monic divisors of the
indexed components. This keeps distinct positions when components repeat. -/
theorem split_monic_product {ι K : Type*} [DecidableEq ι] [Field K] (S : Finset ι)
    (A : ι → K[X]) {f : K[X]} (fm : f.Monic) (dvd : f ∣ ∏ i ∈ S, A i) :
    ∃ u : ι → K[X], (∀ i ∈ S, (u i).Monic ∧ u i ∣ A i) ∧ f = ∏ i ∈ S, u i := by
  classical
  induction S using Finset.induction_on generalizing f with
  | empty =>
    simp only [prod_empty] at dvd ⊢
    exact ⟨fun _ => 1,by simp, fm.eq_one_of_isUnit (isUnit_of_dvd_one dvd)⟩
  | @insert i S fresh ih =>
    rw [prod_insert fresh] at dvd
    obtain ⟨u,v,um,vm,du,dv,eq⟩ := Green28PrimeFactors.split_monic_divisor fm dvd
    obtain ⟨w,hw,hv⟩ := ih vm dv
    refine ⟨Function.update w i u,?_,?_⟩
    · intro j hj
      rcases mem_insert.mp hj with rfl | hj
      · simpa using And.intro um du
      · have ne : j ≠ i := fun e => fresh (e ▸ hj)
        simpa only [Function.update_of_ne ne] using hw j hj
    · rw [prod_insert fresh,Function.update_self,eq,hv]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      exact (Function.update_of_ne (fun e : j = i => fresh (e ▸ hj)) u w).symm

private theorem lift_monic_divisor {L : Type} [Field L] [CharZero L] {H : ℤ[X]} (hm : H.Monic)
    {u : L[X]} (um : u.Monic) (dvd : u ∣ H.map (Int.castRingHom L)) :
    ∃ U : (integralClosure ℤ L)[X], U.Monic ∧ U.map (integralClosure ℤ L).toSubring.subtype = u ∧
      U ∣ H.map (Int.castRingHom (integralClosure ℤ L)) := by
  let T := (integralClosure ℤ L).toSubring
  have inside : (u.coeffs : Set L) ⊆ T := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
    exact isIntegral_coeff_of_dvd H u hm um dvd i
  let U := u.toSubring T inside
  have m : U.Monic := (monic_toSubring _ _ _).mpr um
  have eq : U.map T.subtype = u := map_toSubring _ _ _
  refine ⟨U,m,eq,(map_dvd_map T.subtype Subtype.val_injective m).mp ?_⟩
  rwa [eq,Polynomial.map_map,RingHom.ext_int (T.subtype.comp _) (Int.castRingHom L)]

/-- In characteristic zero each monic divisor with constant term one is a
subproduct of the given integral components. Their signed root orders at
a single prime are pairwise coprime and their indices are small. -/
theorem subproduct_of_coprime_orbits {L ι : Type} [Field L] [CharZero L] [Fintype ι]
    {p : ℕ} [Fact p.Prime] (A : ι → ℤ[X]) (d n c : ι → ℕ) (am : ∀ i, (A i).Monic)
    (orbit : ∀ i, PrimeOrbit (A i) p (d i) (n i))
    (index : ∀ i, n i*c i = digitSum p (range (d i))) (small : ∀ i, c i ≤ p)
    (cop : Pairwise (fun i j => (n i).Coprime (n j))) {f : L[X]} (fm : f.Monic)
    (one : f.coeff 0 = 1) (dvd : f ∣ ∏ i, (A i).map (Int.castRingHom L)) :
    ∃ I : Finset ι, f = ∏ i ∈ I, (A i).map (Int.castRingHom L) := by
  classical
  obtain ⟨u,divs,split⟩ := split_monic_product univ _ fm dvd
  have du (i : ι) := divs i (mem_univ i)
  choose U mon eqU dU using fun i => lift_monic_divisor (am i) (du i).1 (du i).2
  let T := (integralClosure ℤ L).toSubring
  have constant : ∏ i, (U i).coeff 0 = 1 := by
    apply T.subtype_injective
    rw [map_prod,map_one]
    dsimp only [T]
    simpa only [←Polynomial.coeff_map,eqU,←coeff_zero_prod,←split] using one
  apply with_prime_residue L p
  intro K fld cp closed φ
  let V := fun i => (U i).map φ
  have vd (i : ι) : V i ∣ (A i).map (Int.castRingHom K) := by
    have h := _root_.map_dvd (Polynomial.mapRingHom φ) (dU i)
    change (U i).map φ ∣ ((A i).map (Int.castRingHom _)).map φ at h
    simpa only [V,Polynomial.map_map,RingHom.ext_int (φ.comp _) (Int.castRingHom K)] using h
  have test (i : ι) := divisor_constant (am i) (orbit i) (index i) (small i) ((mon i).map φ) (vd i)
  have all1 : ∏ i, (V i).coeff 0 = 1 := by
    simpa only [V,coeff_map,map_prod,map_one] using congrArg φ constant
  have term := constants_of_coprime_orders univ (fun i => (V i).coeff 0) n
    (fun i _ => (test i).1) (fun _ _ _ _ h => cop h) all1
  have whole (i : ι) : u i = 1 ∨ u i = (A i).map (Int.castRingHom L) := by
    have deg : (u i).natDegree = (V i).natDegree := by
      rw [←eqU i,(mon i).natDegree_map,(mon i).natDegree_map]
    rcases (test i).2 (term i (mem_univ i)) with empty | full
    · change V i = 1 at empty
      exact Or.inl ((du i).1.natDegree_eq_zero.mp (by rw [deg,empty,natDegree_one]))
    · change V i = (A i).map (Int.castRingHom K) at full
      exact Or.inr (eq_of_monic_of_dvd_of_natDegree_le (du i).1 ((am i).map _) (du i).2
        (by rw [deg,full,(am i).natDegree_map,(am i).natDegree_map])).symm
  refine ⟨univ.filter (fun i => u i ≠ 1),split.trans ?_⟩
  rw [prod_filter]
  apply prod_congr rfl
  intro i _
  by_cases trivial : u i = 1
  · simp only [trivial,ne_self_iff_false,if_false]
  · rw [if_pos trivial]
    exact (whole i).resolve_left trivial

open Green28 Green28UniformSums Green28PolynomialReduction

/-- Every independent decomposition of the observed uniform law partitions
the given components between its normalized marginal polynomials. -/
theorem marginal_subproducts {ι : Type} [Fintype ι] [DecidableEq ι]
    {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne)
    {p : ℕ} [Fact p.Prime] (A : ι → ℤ[X]) (d n c : ι → ℕ)
    (mask : outputMask S ne = ∏ i, A i) (am : ∀ i, (A i).Monic)
    (orbit : ∀ i, PrimeOrbit (A i) p (d i) (n i))
    (index : ∀ i, n i*c i = digitSum p (range (d i))) (small : ∀ i, c i ≤ p)
    (cop : Pairwise (fun i j => (n i).Coprime (n j))) :
    ∃ (I : Finset ι) (a b : ℤ) (s t : ℝ),
      Models P ((∏ i ∈ I, A i).map (Int.castRingHom ℝ)) a s ∧
      Models Q ((∏ i ∈ univ \ I, A i).map (Int.castRingHom ℝ)) b t ∧
      IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  classical
  obtain ⟨f,g,a,b,s,t,fp,gp,fm,gm,_,_,f0,_,prod⟩ := mask_factorization ne sum
  rw [mask,Polynomial.map_prod] at prod
  obtain ⟨I,selection⟩ := subproduct_of_coprime_orbits A d n c am orbit index small cop fm f0
    (prod ▸ dvd_mul_right f g)
  have rest : g = (∏ i ∈ univ \ I, A i).map (Int.castRingHom ℝ) := by
    apply mul_left_cancel₀ fm.ne_zero
    rw [prod,selection,Polynomial.map_prod,mul_comm,prod_sdiff (subset_univ I)]
  rw [←Polynomial.map_prod] at selection
  have bin := ((fp.mul gp).uniform_iff (fm.mul gm)).mp ⟨S,ne,sum⟩
  have rat (i : ℕ) : ∃ q : ℚ, (q:ℝ) = f.coeff i := by
    refine ⟨((∏ j ∈ I, A j).coeff i : ℚ),?_⟩
    rw [selection,coeff_map]
    simp
  obtain ⟨fb,gb⟩ := rational_factor fm gm fp.nonneg gp.nonneg bin rat
  exact ⟨I,a,b,s,t,selection ▸ fp,rest ▸ gp,(fp.uniform_iff fm).mpr fb,(gp.uniform_iff gm).mpr gb⟩

#print axioms marginal_subproducts
#print axioms subproduct_of_coprime_orbits
#print axioms divisor_constant
#print axioms constants_of_coprime_orders
#print axioms split_monic_product
end Green28CoprimeOrbitFactors
