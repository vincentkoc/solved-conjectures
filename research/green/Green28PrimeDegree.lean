import Green28PrimitiveSupport
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Prime-degree conjugate-product obstructions for Green 28. -/

namespace Green28PrimeDegree

open Polynomial Finset

/-- A cyclic shift of prime order is detected by any integer weight whose
sum is nonzero modulo that prime. -/
private theorem weight_coprime {p : ℕ} (hp : p.Prime) (F : ℤ[X])
    (unitWeight : ¬ (p:ℤ) ∣ F.eval 1) :
    IsCoprime ((X:ℚ[X])^p-1) (F.map (Int.castRingHom ℚ)) := by
  let _ : Fact p.Prime := ⟨hp⟩
  rw [←cyclotomic_prime_mul_X_sub_one ℚ p]
  apply IsCoprime.mul_left
  · apply (cyclotomic.irreducible_rat hp.pos).coprime_iff_not_dvd.mpr
    intro h
    have hd : cyclotomic p ℤ ∣ F := by
      apply (map_dvd_map (Int.castRingHom ℚ) Int.cast_injective (cyclotomic.monic p ℤ)).mp
      simpa using h
    have e := eval_dvd (x := (1:ℤ)) hd
    exact unitWeight (by simpa [eval_one_cyclotomic_prime] using e)
  · have irr : Irreducible ((X:ℚ[X])-1) := by simpa using irreducible_X_sub_C (1:ℚ)
    apply irr.coprime_iff_not_dvd.mpr
    intro h
    have hd : X - C (1:ℤ) ∣ F := by
      apply (map_dvd_map (Int.castRingHom ℚ) Int.cast_injective (monic_X_sub_C (1:ℤ))).mp
      simpa using h
    exact unitWeight (by rw [(dvd_iff_isRoot.mp hd : F.eval 1 = 0)]; exact dvd_zero _)

/-- If a vector is periodic with prime period dividing `p`, a vanishing
weighted sum of its translates must have weight divisible by `p`. -/
private theorem periodic_kernel {V : Type*} [AddCommGroup V] [Module ℚ V]
    {p : ℕ} (hp : p.Prime) (F : ℤ[X]) (weight : ¬ (p:ℤ) ∣ F.eval 1)
    (T : Module.End ℚ V) (v : V) (period : (T^p) v = v)
    (vanish : (aeval T (F.map (Int.castRingHom ℚ))) v=0) : v=0 := by
  obtain ⟨A,B,bezout⟩ := weight_coprime hp F weight
  have z : (aeval T ((X:ℚ[X])^p-1)) v=0 := by simp [period]
  have h := congrArg (fun P : ℚ[X] => (aeval T P) v) bezout
  simpa only [map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply, z, vanish,
    map_zero, add_zero, map_one, Module.End.one_apply] using h.symm

private def shift : Module.End ℚ (ℕ → ℝ) where
  toFun v n := v (n+1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem shift_pow (v : ℕ → ℝ) (i n : ℕ) : (shift^i) v n = v (n+i) := by
  induction i generalizing n with
  | zero => simp
  | succ i ih => rw [pow_succ',Module.End.mul_apply]; change (shift^i) v (n+1) = _; rw [ih]; congr 1; omega

private theorem cyclic_sum {p : ℕ} (hp : p.Prime) (I : Finset ℕ)
    (pos : 0<I.card) (small : I.card<p) (u : ℕ → ℝ)
    (period : ∀ n, u (n+p)=u n) (vanish : ∀ n, ∑ i ∈ I, u (n+i)=0) : u=0 := by
  let F : ℤ[X] := ∑ i ∈ I, X^i
  apply periodic_kernel hp F _ shift u
  · funext n; exact (shift_pow u p n).trans (period n)
  · funext n
    simpa [F, Polynomial.map_sum, LinearMap.sum_apply, Finset.sum_apply, shift_pow] using vanish n
  · simpa [F,Polynomial.eval_finsetSum] using (show ¬(p:ℤ)∣(I.card:ℤ) by exact_mod_cast Nat.not_dvd_of_pos_of_lt pos small)

private theorem prime_cycle (H : ℚ[X]) (irr : Irreducible H) (hp : H.natDegree.Prime) :
    ∃ σ : H.Gal, σ^H.natDegree=1 ∧ ∀ x y : H.rootSet H.SplittingField,
      ∃ i < H.natDegree, (σ^i) x.val=y.val := by
  classical
  let _ : Fact H.natDegree.Prime := ⟨hp⟩
  let ρ := @MulAction.toPermHom H.Gal (H.rootSet H.SplittingField) _ (Gal.galActionAux H)
  have faithful : Function.Injective ρ := by
    intro a b h
    apply Gal.ext H
    intro z hz
    exact congrArg Subtype.val (DFunLike.congr_fun h ⟨z,hz⟩)
  obtain ⟨σ,ho⟩ := exists_prime_orderOf_dvd_card' H.natDegree (Gal.prime_degree_dvd_card irr hp)
  have card := card_rootSet_eq_natDegree irr.separable (SplittingField.splits H)
  have ord : orderOf (ρ σ)=H.natDegree := (orderOf_injective ρ faithful σ).trans ho
  have cyc := Equiv.Perm.isCycle_of_prime_order'' (card ▸ hp) (ord.trans card.symm)
  have full : (ρ σ).support=univ := eq_univ_of_card _ <| (cyc.orderOf.symm.trans ord).trans card.symm
  have moves (x : H.rootSet H.SplittingField) : ρ σ x≠x :=
    Equiv.Perm.mem_support.mp (full ▸ mem_univ x)
  refine ⟨σ,ho ▸ pow_orderOf_eq_one σ,fun x y => ?_⟩
  obtain ⟨n,hn⟩ := cyc.exists_pow_eq (moves x) (moves y)
  refine ⟨n%H.natDegree,Nat.mod_lt _ hp.pos,?_⟩
  have h : (ρ (σ^(n%H.natDegree))) x=y := by
    rw [map_pow,←ord,pow_mod_orderOf,hn]
  exact congrArg Subtype.val h

private theorem orbit_factors (H : ℚ[X]) (hm : H.Monic) (irr : Irreducible H)
    (σ : H.Gal) (x : H.rootSet H.SplittingField)
    (covers : ∀ y : H.rootSet H.SplittingField, ∃ i < H.natDegree, (σ^i) x.val=y.val) :
    H.map (algebraMap ℚ H.SplittingField)=∏ i ∈ range H.natDegree, (X-C ((σ^i) x.val)) := by
  classical
  let K := H.SplittingField
  let a (i : ℕ) : K := (σ^i) x.val
  let L : K[X] := ∏ i ∈ range H.natDegree, (X-C (a i))
  have lm : L.Monic := monic_prod_X_sub_C a _
  have dv : H.map (algebraMap ℚ K) ∣ L := by
    apply (SplittingField.splits H).dvd_of_roots_le_roots (map_ne_zero irr.ne_zero)
    apply (Multiset.le_iff_subset (nodup_roots irr.separable.map)).mpr
    intro z hz
    have mem : z∈H.rootSet K := by
      apply (mem_rootSet_of_ne irr.ne_zero).mpr
      rw [← eval_map_algebraMap]
      exact (mem_roots (map_ne_zero irr.ne_zero)).mp hz
    obtain ⟨i,hi,hit⟩ := covers ⟨z,mem⟩
    apply (mem_roots lm.ne_zero).mpr
    apply dvd_iff_isRoot.mp
    change X-C z ∣ ∏ j ∈ range H.natDegree, (X-C (a j))
    change a i = z at hit
    rw [←hit]
    exact Finset.dvd_prod_of_mem _ (mem_range.mpr hi)
  exact (eq_of_monic_of_dvd_of_natDegree_le (hm.map _) lm dv
    (by simp [L,natDegree_finsetProd_X_sub_C_eq_card])).symm

private theorem orbit_norm {K : Type*} [Field K] [Algebra ℚ K]
    {p : ℕ} (hp : p.Prime) (σ : K ≃ₐ[ℚ] K) (sp : σ^p=1) (ι : K →ₐ[ℚ] ℂ)
    (x : K) (hx : x≠0) (I : Finset ℕ) (pos : 0<I.card) (small : I.card<p)
    (relation : ∏ i ∈ I, -ι ((σ^i) x)=1) : ∀ n : ℕ, ‖ι ((σ^n) x)‖=1 := by
  let u (n : ℕ) := Real.log ‖ι ((σ^n) x)‖
  have nz (n : ℕ) : ι ((σ^n) x)≠0 := by simpa only [_root_.map_ne_zero] using hx
  have base : ∏ i ∈ I, -((σ^i) x)=1 := ι.injective (by simpa using relation)
  have van (n : ℕ) : ∑ i ∈ I, u (n+i)=0 := by
    have shiftRel := congrArg (fun a : K => ι ((σ^n) a)) base
    have prodRel : ∏ i ∈ I, ‖ι ((σ^(n+i)) x)‖=1 := by
      have h := congrArg (fun z : ℂ => ‖z‖) shiftRel
      simpa [map_prod, norm_prod, pow_add,AlgEquiv.mul_apply] using h
    change ∑ i ∈ I, Real.log ‖ι ((σ^(n+i)) x)‖=0
    rw [← Real.log_prod (fun i _ => norm_ne_zero_iff.mpr (nz (n+i))),prodRel,Real.log_one]
  have periodic (n : ℕ) : u (n+p)=u n := by simp only [u,pow_add,sp,mul_one]
  have zero := cyclic_sum hp I pos small u periodic van
  intro n
  exact Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.mpr (nz n)) (congrFun zero n)

private theorem real_root_of_odd (H : ℚ[X]) (irr : Irreducible H) (odd : Odd H.natDegree) :
    ∃ r : ℝ, aeval r H=0 := by
  classical
  let _ : Fact ((H.map (algebraMap ℚ ℂ)).Splits) := ⟨IsAlgClosed.splits _⟩
  let τ := Gal.galActionHom H ℂ (Gal.restrict H ℂ (Complex.conjAe.restrictScalars ℚ))
  have ev : 2 ∣ τ.support.card := Equiv.Perm.two_dvd_card_support (by
    dsimp only [τ]
    rw [←map_pow,←map_pow,show (Complex.conjAe.restrictScalars ℚ)^2=1 from AlgEquiv.ext Complex.conj_conj,
      map_one,map_one])
  have count := Gal.card_complex_roots_eq_card_real_add_card_not_gal_inv H
  change _ = _ + τ.support.card at count
  simp only [Set.toFinset_card] at count
  have card := card_rootSet_eq_natDegree irr.separable (K:=ℂ) (IsAlgClosed.splits _)
  have pos : 0<Fintype.card (H.rootSet ℝ) := by grind [Odd]
  obtain ⟨r⟩ := Fintype.card_pos_iff.mp pos
  exact ⟨r.val, (mem_rootSet.mp r.property).2⟩

private theorem no_rational_root (H : ℚ[X]) (irr : Irreducible H) (hp : H.natDegree.Prime)
    (r : ℚ) : H.eval r ≠ 0 := by
  intro h
  have d := (irreducible_X_sub_C r).dvd_symm irr (dvd_iff_isRoot.mpr h)
  have le := natDegree_le_of_dvd d (monic_X_sub_C r).ne_zero
  simp only [natDegree_X_sub_C] at le
  exact (not_lt_of_ge le) hp.one_lt

/-- In a monic rational polynomial irreducible of prime degree, a monic
complex factor with constant coefficient one is trivial or has full degree. -/
theorem no_unit_constant_split (H : ℚ[X]) (hm : H.Monic) (irr : Irreducible H)
    (hp : H.natDegree.Prime) {f g : ℂ[X]} (fm : f.Monic) (gm : g.Monic)
    (f0 : f.coeff 0=1) (factor : f*g=H.map (algebraMap ℚ ℂ)) :
    f.natDegree=0 ∨ g.natDegree=0 := by
  classical
  by_contra! bad
  have deg : f.natDegree+g.natDegree=H.natDegree := by
    rw [←natDegree_mul fm.ne_zero gm.ne_zero,factor,hm.natDegree_map]
  obtain ⟨σ,period,covers⟩ := prime_cycle H irr hp
  let ι : H.SplittingField →ₐ[ℚ] ℂ := SplittingField.lift H (IsAlgClosed.splits _)
  have card := card_rootSet_eq_natDegree irr.separable (SplittingField.splits H)
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp (card ▸ hp.pos)
  let a (i : ℕ) := ι ((σ^i) x.val)
  have eq : H.map (algebraMap ℚ ℂ)=∏ i ∈ range H.natDegree, (X-C (a i)) := by
    have h := congrArg (Polynomial.map ι.toRingHom) (orbit_factors H hm irr σ x (covers x))
    rw [Polynomial.map_map] at h
    have comp : ι.toRingHom.comp (algebraMap ℚ H.SplittingField)=algebraMap ℚ ℂ := ι.comp_algebraMap
    rw [comp] at h
    simp only [Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C] at h
    apply h.trans
    apply Finset.prod_congr rfl
    intro i _
    rfl
  obtain ⟨I,sub,fe⟩ := Green28PrimitiveSupport.divisor_subproduct a _ fm gm (factor.trans eq)
  have count : f.natDegree=I.card := by rw [fe,natDegree_finsetProd_X_sub_C_eq_card]
  have pos : 0<I.card := by omega
  have small : I.card<H.natDegree := by omega
  have unit : ∏ i ∈ I, -a i = 1 := by
    rw [coeff_zero_eq_eval_zero,fe,eval_prod] at f0
    simpa only [eval_sub,eval_X,eval_C,zero_sub] using f0
  have norat (q : ℚ) : aeval (algebraMap ℚ ℂ q) H ≠ 0 := by
    rw [aeval_algebraMap_apply_eq_algebraMap_eval]
    exact (_root_.map_ne_zero _).mpr (no_rational_root H irr hp q)
  have root (i : ℕ) (hi : i∈I) : aeval (a i) H=0 := by
    rw [←eval_map_algebraMap,eq,eval_prod,Finset.prod_eq_zero_iff]
    exact ⟨i,sub hi,by simp⟩
  rcases hp.eq_two_or_odd with two|odd
  · obtain ⟨i,hi⟩ := Finset.card_eq_one.mp (show I.card=1 by omega)
    have sign : -a i=1 := by simpa [hi] using unit
    have minus : a i=(-1:ℂ) := by linear_combination -sign
    have rt := root i (hi ▸ mem_singleton_self _)
    exact norat (-1) (by simpa only [map_neg,map_one,minus] using rt)
  · have xn : x.val≠0 := by
      intro hz
      obtain ⟨i,hi⟩ := Finset.card_pos.mp pos
      have zero : ∏ j ∈ I, -a j = 0 := Finset.prod_eq_zero hi (by simp [a,hz])
      exact zero_ne_one (zero.symm.trans unit)
    have norms := orbit_norm hp σ period ι x.val xn I pos small unit
    obtain ⟨r,hr⟩ := real_root_of_odd H irr (Nat.odd_iff.mpr odd)
    have rc : aeval (algebraMap ℝ ℂ r) H=0 := by rw [aeval_algebraMap_apply,hr,map_zero]
    have rc0 := rc
    rw [←eval_map_algebraMap,eq,eval_prod,Finset.prod_eq_zero_iff] at rc
    obtain ⟨i,_,hi⟩ := rc
    have rv : (r:ℂ)=a i := by
      change (algebraMap ℝ ℂ r) = a i
      exact sub_eq_zero.mp (by simpa only [eval_sub,eval_X,eval_C] using hi)
    have abs : |r|=1 := by
      rw [←Real.norm_eq_abs,←Complex.norm_real,rv]; exact norms i
    rcases (abs_eq (by norm_num : (0:ℝ)≤1)).mp abs with e|e
    · subst r
      exact norat 1 (by simpa only [map_neg,map_one] using rc0)
    · subst r
      exact norat (-1) (by simpa only [map_neg,map_one] using rc0)

open Green28 Green28PrimitiveSupport

/-- A prime-width, rationally irreducible integer output mask forces a
point-mass input, with no restriction on the two original marginals. -/
theorem pure_factor_of_prime_degree {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q=PMF.uniformOfFinset S ne)
    (prime : (outputMask S ne).natDegree.Prime)
    (irr : Irreducible ((outputMask S ne).map (Int.castRingHom ℚ))) :
    (∃ x, P=PMF.pure x) ∨ (∃ y, Q=PMF.pure y) := by
  apply pure_factor_of_mask ne sum
  intro mon f g fm gm f0 fg
  let H := outputMask S ne
  let R := H.map (Int.castRingHom ℚ)
  let t := algebraMap ℝ ℂ
  have h : (f.map t)*(g.map t)=R.map (algebraMap ℚ ℂ) := by
    rw [←Polynomial.map_mul,fg,Polynomial.map_map]
    change H.map _=(H.map _).map _
    rw [Polynomial.map_map]
    exact congrArg (fun φ : ℤ →+* ℂ => H.map φ) (RingHom.ext_int _ _)
  have pc : R.natDegree.Prime := by
    change ((outputMask S ne).map (Int.castRingHom ℚ)).natDegree.Prime
    rwa [mon.natDegree_map]
  have z := no_unit_constant_split R (mon.map _) irr pc (fm.map t) (gm.map t)
    (by rw [coeff_map,f0,map_one]) h
  simpa only [fm.natDegree_map,gm.natDegree_map] using z

/-- Green 28 with prime-width irreducible output mask in the original
integer probability predicates. -/
theorem uniform_of_prime_degree {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q=PMF.uniformOfFinset S ne)
    (prime : (outputMask S ne).natDegree.Prime)
    (irr : Irreducible ((outputMask S ne).map (Int.castRingHom ℚ))) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q :=
  uniform_of_pure_factor ⟨S,ne,sum⟩ (pure_factor_of_prime_degree ne sum prime irr)

#print axioms Green28PrimitiveSupport.pure_factor_of_mask
#print axioms Green28PrimitiveSupport.uniform_of_pure_factor
#print axioms no_unit_constant_split
#print axioms pure_factor_of_prime_degree
#print axioms uniform_of_prime_degree

end Green28PrimeDegree
