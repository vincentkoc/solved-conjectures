import Green28PrimeDegree
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.Data.Nat.Prime.Factorial

/-! Removing irreducible factors of distinct prime degrees from Green 28 output masks. -/

namespace Green28PrimeFactors

open Polynomial Finset

/-- A common factorial power fixes every root of every rational polynomial
of degree at most `d`. -/
private theorem fixed_small_root {L : Type*} [Field L] [Algebra ℚ L] [IsAlgClosed L]
    (τ : L ≃ₐ[ℚ] L) (d : ℕ) (H : ℚ[X]) (small : H.natDegree≤d)
    (x : H.rootSet L) : (τ^d.factorial) x.val=x.val := by
  classical
  let _ : Fact ((H.map (algebraMap ℚ L)).Splits) := ⟨IsAlgClosed.splits _⟩
  let ρ := (Gal.galActionHom H L).comp (Gal.restrict H L)
  have card : Fintype.card (H.rootSet L)≤d := by
    have h := H.ncard_rootSet_le L
    rw [Set.ncard_eq_toFinset_card',Set.toFinset_card] at h
    exact h.trans small
  have dvd : orderOf (ρ τ) ∣ d.factorial := by
    apply orderOf_dvd_card.trans
    rw [Fintype.card_perm]
    exact Nat.factorial_dvd_factorial card
  have one : ρ (τ^d.factorial)=1 := by
    rw [map_pow,orderOf_dvd_iff_pow_eq_one.mp dvd]
  have h := Gal.galActionHom_restrict H L (τ^d.factorial) x
  change ((ρ (τ^d.factorial) x).val : L) = _ at h
  rw [one] at h
  exact h.symm

/-- A prime-degree irreducible factor has a full cycle that fixes every
root of every rational polynomial of smaller degree. -/
private theorem isolating_cycle {L : Type*} [Field L] [Algebra ℚ L] [IsAlgClosed L] [Normal ℚ L]
    (H : ℚ[X]) (irr : Irreducible H) (hp : H.natDegree.Prime) :
    ∃ τ : L ≃ₐ[ℚ] L, (∀ x : H.rootSet L, (τ^H.natDegree) x.val=x.val) ∧
      (∀ x y : H.rootSet L, ∃ i < H.natDegree, (τ^i) x.val=y.val) ∧
      ∀ C : ℚ[X], C.natDegree<H.natDegree → ∀ x : C.rootSet L, τ x.val=x.val := by
  classical
  let _ : Fact ((H.map (algebraMap ℚ L)).Splits) := ⟨IsAlgClosed.splits _⟩
  let _ : Fact H.natDegree.Prime := ⟨hp⟩
  let φ := Gal.galActionHom H L
  let ρ := φ.comp (Gal.restrict H L)
  obtain ⟨σ,ord⟩ := exists_prime_orderOf_dvd_card' H.natDegree (Gal.prime_degree_dvd_card irr hp)
  have ord' : orderOf (φ σ)=H.natDegree :=
    (orderOf_injective φ (Gal.galActionHom_injective H L) σ).trans ord
  obtain ⟨s,hs⟩ := Gal.restrict_surjective H L σ
  let N := (H.natDegree-1).factorial
  have cop : H.natDegree.Coprime N := hp.coprime_iff_not_dvd.mpr fun h =>
    (by have := hp.pos; omega : ¬H.natDegree≤H.natDegree-1) (hp.dvd_factorial.mp h)
  let τ := s^N
  have o : orderOf (ρ τ)=H.natDegree := by
    change orderOf (ρ (s^N))=_
    rw [map_pow,show ρ s=φ σ from congrArg φ hs,(ord' ▸ cop : (orderOf (φ σ)).Coprime N).orderOf_pow,ord']
  have card := card_rootSet_eq_natDegree irr.separable (K:=L) (IsAlgClosed.splits _)
  have cyc := Equiv.Perm.isCycle_of_prime_order'' (card ▸ hp) (o.trans card.symm)
  have full : (ρ τ).support=univ := eq_univ_of_card _ <| (cyc.orderOf.symm.trans o).trans card.symm
  have moves (x : H.rootSet L) : ρ τ x≠x := Equiv.Perm.mem_support.mp (full ▸ mem_univ x)
  have act (i : ℕ) (x : H.rootSet L) : ((ρ τ^i) x).val=(τ^i) x.val := by
    rw [←map_pow]; exact Gal.galActionHom_restrict H L _ x
  refine ⟨τ,fun x => ?_,fun x y => ?_,fun C hc x => fixed_small_root s _ C (by omega) x⟩
  · have a := act H.natDegree x
    rw [←o,pow_orderOf_eq_one] at a
    simpa [o] using a.symm
  · obtain ⟨n,hn⟩ := cyc.exists_pow_eq (moves x) (moves y)
    refine ⟨n%H.natDegree,Nat.mod_lt _ hp.pos,?_⟩
    rw [←act,←o,pow_mod_orderOf,hn]

private theorem constant_of_shift_sums {p : ℕ} (hp : p.Prime) (I : Finset ℕ)
    (pos : 0<I.card) (small : I.card<p) (u : ℕ → ℝ) (c : ℝ)
    (period : ∀ n, u (n+p)=u n) (sums : ∀ n, ∑ i ∈ I, u (n+i)=c) :
    ∀ n, u n=u 0 := by
  let v (n : ℕ) := u (n+1)-u n
  have per (n : ℕ) : v (n+p)=v n := by
    change u (n+p+1)-u (n+p)=_
    rw [show n+p+1=n+1+p by omega,period,period]
  have van (n : ℕ) : ∑ i ∈ I, v (n+i)=0 := by
    change ∑ i ∈ I, (u (n+i+1)-u (n+i))=0
    simp_rw [show ∀ i : ℕ, n+i+1=n+1+i by omega]
    rw [sum_sub_distrib,sums,sums,sub_self]
  have z := Green28PrimeDegree.cyclic_sum hp I pos small v per van
  intro n
  induction n with
  | zero => rfl
  | succ n ih => exact (sub_eq_zero.mp (congrFun z n)).trans ih
private theorem fixed_powers {K : Type*} [Field K] [Algebra ℚ K] (τ : K ≃ₐ[ℚ] K)
    {x : K} (fix : τ x=x) (i : ℕ) : (τ^i) x=x := by
  induction i with
  | zero => rfl
  | succ i ih => rw [pow_succ',AlgEquiv.mul_apply,ih,fix]


private theorem unit_norms_of_fixed_product {K : Type*} [Field K] [Algebra ℚ K]
    {p : ℕ} (hp : p.Prime) (τ : K ≃ₐ[ℚ] K) (ι : K →ₐ[ℚ] ℂ)
    (x : K) (nz : x≠0) (per : (τ^p) x=x) (I : Finset ℕ) (pos : 0<I.card)
    (small : I.card<p) (c : K) (fix : τ c=c) (part : ∏ i ∈ I, -((τ^i) x)=c)
    (full : ‖ι (∏ i ∈ range p, -((τ^i) x))‖=1) : ∀ n : ℕ, ‖ι ((τ^n) x)‖=1 := by
  let u (n : ℕ) := Real.log ‖ι ((τ^n) x)‖
  have ne (n : ℕ) : ι ((τ^n) x)≠0 := by simpa only [_root_.map_ne_zero] using nz
  have pw := fixed_powers τ fix
  have sums (n : ℕ) : ∑ i ∈ I, u (n+i)=Real.log ‖ι c‖ := by
    have eq := congrArg (fun a : K => ‖ι ((τ^n) a)‖) part
    change ∑ i ∈ I, Real.log ‖ι ((τ^(n+i)) x)‖=_
    rw [←Real.log_prod (fun i _ => norm_ne_zero_iff.mpr (ne (n+i)))]
    apply congrArg Real.log
    simpa only [map_prod,map_neg,norm_prod,norm_neg,pow_add,AlgEquiv.mul_apply,pw] using eq
  have period (n : ℕ) : u (n+p)=u n := by simp only [u,pow_add,AlgEquiv.mul_apply,per]
  have con := constant_of_shift_sums hp I pos small u _ period sums
  have total : ∑ i ∈ range p, u i=0 := by
    change ∑ i ∈ range p, Real.log ‖ι ((τ^i) x)‖=0
    rw [←Real.log_prod (fun i _ => norm_ne_zero_iff.mpr (ne i))]
    have h := congrArg Real.log full
    simpa only [map_prod,map_neg,norm_prod,norm_neg,Real.log_one] using h
  have z : u 0=0 := by
    simp_rw [con] at total
    simpa [hp.ne_zero] using total
  exact fun n => Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.mpr (ne n)) ((con n).trans z)

private abbrev AlgNums := ↥(algebraicClosure ℚ ℂ)
private noncomputable abbrev emb : AlgNums →ₐ[ℚ] ℂ := (algebraicClosure ℚ ℂ).val
local instance : IsAlgClosure ℚ AlgNums := algebraicClosure.isAlgClosure ℚ ℂ
local instance : IsAlgClosed AlgNums := IsAlgClosure.isAlgClosed ℚ
local instance : Normal ℚ AlgNums := IsAlgClosure.normal ℚ AlgNums

private theorem const_of_linear_factors {K : Type*} [Field K] {u : K[X]} {I : Finset ℕ}
    (a : ℕ → K) (eq : u=∏ i ∈ I, (X-C (a i))) : u.coeff 0=∏ i ∈ I, -a i := by
  rw [coeff_zero_eq_eval_zero,eq,eval_prod]
  simp only [eval_sub,eval_X,eval_C,zero_sub]

private theorem impossible_unit_circle (H : ℚ[X]) (irr : Irreducible H) (hp : H.natDegree.Prime)
    (odd : Odd H.natDegree) (unit : ∀ z : H.rootSet AlgNums, ‖emb z.val‖=1) : False := by
  obtain ⟨r,hr⟩ := Green28PrimeDegree.real_root_of_odd H irr odd
  have rc : aeval (algebraMap ℝ ℂ r) H=0 := by rw [aeval_algebraMap_apply,hr,map_zero]
  let a : AlgNums := ⟨algebraMap ℝ ℂ r,mem_algebraicClosure_iff.mpr ⟨H,irr.ne_zero,rc⟩⟩
  have ra : a∈H.rootSet AlgNums := by
    apply (mem_rootSet_of_ne irr.ne_zero).mpr
    exact emb.injective ((aeval_algHom_apply emb a H).symm.trans (rc.trans (map_zero emb).symm))
  have ab : |r|=1 := by
    rw [← Real.norm_eq_abs, ←Complex.norm_real]; exact unit ⟨a,ra⟩
  have no (q : ℚ) : aeval (algebraMap ℚ ℂ q) H ≠0 := by
    rw [aeval_algebraMap_apply_eq_algebraMap_eval]
    exact (_root_.map_ne_zero _).mpr (Green28PrimeDegree.no_rational_root H irr hp q)
  rcases (abs_eq (by norm_num : (0:ℝ)≤1)).mp ab with e|e
  · subst r; exact no 1 (by simpa only [map_one] using rc)
  · subst r; exact no (-1) (by simpa only [map_neg,map_one] using rc)

private theorem whole_component (H : ℚ[X]) (hm : H.Monic) (irr : Irreducible H)
    (hp : H.natDegree.Prime) (h0 : H.coeff 0=1 ∨ H.coeff 0= -1)
    (τ : AlgNums ≃ₐ[ℚ] AlgNums) (period : ∀ x : H.rootSet AlgNums, (τ^H.natDegree) x.val=x.val)
    (covers : ∀ x y : H.rootSet AlgNums, ∃ i < H.natDegree, (τ^i) x.val=y.val)
    (u : AlgNums[X]) (um : u.Monic) (du : u ∣ H.map (algebraMap ℚ AlgNums)) (fix : τ (u.coeff 0)=u.coeff 0) :
    u=1 ∨ u=H.map (algebraMap ℚ AlgNums) := by
  classical
  obtain ⟨v,hv⟩ := du
  have vm := um.of_mul_monic_left (hv ▸ hm.map (algebraMap ℚ AlgNums))
  have card := card_rootSet_eq_natDegree irr.separable (K:=AlgNums) (IsAlgClosed.splits _)
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp (card ▸ hp.pos)
  let a (i : ℕ) := (τ^i) x.val
  have fac := Green28PrimeDegree.orbit_factors H hm irr (IsAlgClosed.splits _) τ x (covers x)
  obtain ⟨I,sub,fe⟩ := Green28PrimitiveSupport.divisor_subproduct a _ um vm (hv.symm.trans fac)
  by_cases first : I=∅
  · exact Or.inl (by simpa only [first,prod_empty] using fe)
  by_cases all : I=range H.natDegree
  · exact Or.inr (by simpa only [all,fac] using fe)
  have pos := card_pos.mpr (nonempty_iff_ne_empty.mpr first)
  have small : I.card<H.natDegree := by simpa only [card_range] using card_lt_card (ssubset_of_subset_of_ne sub all)
  have part := (const_of_linear_factors a fe).symm
  have total := (const_of_linear_factors a fac).symm
  have full : ‖emb (∏ i ∈ range H.natDegree, -a i)‖=1 := by
    rw [total,coeff_map]
    rcases h0 with h|h <;> simp [h]
  have nz : x.val≠0 := by
    intro z
    have zero : ∏ i ∈ range H.natDegree, -a i=0 := Finset.prod_eq_zero (mem_range.mpr hp.pos) (by simp [a,z])
    simp [zero] at full
  -- A fixed singleton contradicts transitivity. For odd degree, compare all root moduli.
  rcases hp.eq_two_or_odd with two|odd
  · obtain ⟨i,hi⟩ := card_eq_one.mp (show I.card=1 by omega)
    have single : -a i = u.coeff 0 := by simpa [hi] using part
    have fi : τ (a i)=a i := by simpa only [←single,map_neg,neg_inj] using fix
    have root : a i∈H.rootSet AlgNums := rootSet_mapsTo (τ^i).toAlgHom x.property
    let z : H.rootSet AlgNums := ⟨a i,root⟩
    let _ : Nontrivial (H.rootSet AlgNums) := Fintype.one_lt_card_iff_nontrivial.mp (card ▸ hp.one_lt)
    obtain ⟨y,ne⟩ := exists_ne z
    obtain ⟨j,_,eq⟩ := covers z y
    exact False.elim (ne (Subtype.ext (eq.symm.trans (fixed_powers τ fi j))))
  · have norms := unit_norms_of_fixed_product hp τ emb x.val nz (period x) I pos small _ fix part full
    apply False.elim (impossible_unit_circle H irr hp (Nat.odd_iff.mpr odd) ?_)
    intro y
    obtain ⟨i,_,hit⟩ := covers x y
    exact hit ▸ norms i

/-- Split a monic divisor of a product into monic divisors of the two pieces. -/
theorem split_monic_divisor {K : Type*} [Field K] {f A B : K[X]} (fm : f.Monic)
    (dv : f∣A*B) : ∃ u v : K[X], u.Monic ∧ v.Monic ∧ u∣A ∧ v∣B ∧ f=u*v := by
  classical
  obtain ⟨a,b,da,db,eq⟩ := exists_dvd_and_dvd_of_dvd_mul dv
  have nz : a≠0 ∧ b≠0 := mul_ne_zero_iff.mp (eq ▸ fm.ne_zero)
  refine ⟨normalize a, normalize b, monic_normalize nz.1,monic_normalize nz.2,?_,?_,?_⟩
  · simpa using da
  · simpa using db
  · rw [←normalize_mul,←eq,fm.normalize_eq_self]

private theorem fixed_divisor_const {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K]
    (τ : K ≃ₐ[ℚ] K) {f T : K[X]} (fm : f.Monic) (dv : f ∣ T) (nz : T≠0)
    (fixed : ∀ z ∈ T.roots, τ z=z) : τ (f.coeff 0)=f.coeff 0 := by
  classical
  have roots := (IsAlgClosed.splits f).eq_prod_roots_of_monic fm
  rw [coeff_zero_eq_eval_zero,roots]
  simp only [eval_multiset_prod,Multiset.map_map,Function.comp_apply,eval_sub,eval_X,eval_C,zero_sub]
  change τ ((f.roots.map (fun z => -z)).prod) = _
  rw [map_multiset_prod,Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro x hx
  change τ (-x)= -x
  rw [map_neg,fixed _ (Multiset.mem_of_le (Polynomial.roots.le_of_dvd nz dv) hx)]

private theorem vanishing_factor (L : List ℚ[X]) (x : AlgNums) (hz : aeval x L.prod=0) :
    ∃ H∈L, aeval x H=0 := by
  induction L with
  | nil => simp at hz
  | cons P L ih =>
    rw [List.prod_cons,map_mul,mul_eq_zero] at hz
    rcases hz with h|h
    · exact ⟨P,List.mem_cons_self,h⟩
    · obtain ⟨H,m,v⟩ := ih h
      exact ⟨H,List.mem_cons_of_mem _ m,v⟩

private theorem list_monic {K : Type*} [Field K] (L : List K[X]) (hm : ∀ H∈L, H.Monic) :
    L.prod.Monic := by
  induction L with
  | nil => simp
  | cons H L ih => exact (hm _ List.mem_cons_self).mul (ih fun P h => hm P (List.mem_cons_of_mem _ h))

/-- A monic linear factor, or a monic irreducible prime-degree factor with unit constant. -/
def PrimeOrLinear (H : ℚ[X]) : Prop :=
  H.Monic ∧ (H.natDegree=1 ∨ Irreducible H ∧ H.natDegree.Prime ∧ (H.coeff 0=1 ∨ H.coeff 0= -1))

private theorem sublist_of_rational_const (L : List ℚ[X]) (good : ∀ H∈L, PrimeOrLinear H)
    (order : L.Pairwise (fun H P => H.natDegree=1 ∨ P.natDegree<H.natDegree))
    (f : AlgNums[X]) (fm : f.Monic) (dv : f ∣ L.prod.map (algebraMap ℚ AlgNums))
    (rat : ∃ q : ℚ, q≠0 ∧ f.coeff 0=algebraMap ℚ AlgNums q) :
    ∃ S : List ℚ[X], S.Sublist L ∧ S.prod.map (algebraMap ℚ AlgNums)=f := by
  classical
  induction L generalizing f with
  | nil =>
    have un : IsUnit f := isUnit_of_dvd_one (by simpa using dv)
    exact ⟨[],.slnil,by simp [fm.eq_one_of_isUnit un]⟩
  | cons H L ih =>
    obtain ⟨hm,kind⟩ := good H List.mem_cons_self
    obtain ⟨less,tail⟩ := List.pairwise_cons.mp order
    have gl (P : ℚ[X]) (h : P∈L) := good P (List.mem_cons_of_mem H h)
    have lm := list_monic L fun P h => (gl P h).1
    rw [List.prod_cons,Polynomial.map_mul] at dv
    obtain ⟨u,v,um,vm,du,dv,fuv⟩ := split_monic_divisor fm dv
    obtain ⟨q,nq,cq⟩ := rat
    rw [fuv,mul_coeff_zero] at cq
    have nz : u.coeff 0≠0 ∧ v.coeff 0≠0 :=
      mul_ne_zero_iff.mp (cq ▸ (_root_.map_ne_zero _).mpr nq)
    -- Remove a whole rational component before recursing on the remaining list.
    have split : u=1 ∨ u=H.map (algebraMap ℚ AlgNums) := by
      rcases kind with lin|⟨irr,hp,h0⟩
      · by_cases uz : u.natDegree=0
        · have co := um.coeff_natDegree
          rw [uz] at co
          exact Or.inl (by rw [eq_C_of_natDegree_eq_zero uz,co,Polynomial.C_1])
        · exact Or.inr (eq_of_monic_of_dvd_of_natDegree_le um (hm.map _) du
            (by rw [hm.natDegree_map,lin]; omega)).symm
      · obtain ⟨τ,per,cyc,fix⟩ := isolating_cycle (L:=AlgNums) H irr hp
        have vf : τ (v.coeff 0)=v.coeff 0 := by
          apply fixed_divisor_const τ vm dv (lm.map _).ne_zero
          intro z hz
          obtain ⟨P,h,eq⟩ := vanishing_factor L z (by
            rw [←eval_map_algebraMap]
            exact (mem_roots (lm.map _).ne_zero).mp hz)
          exact fix P ((less P h).resolve_left hp.ne_one) ⟨z,(mem_rootSet_of_ne (gl P h).1.ne_zero).mpr eq⟩
        have uf : τ (u.coeff 0)=u.coeff 0 := by
          apply mul_right_cancel₀ nz.2
          have eq := congrArg τ cq
          rw [map_mul,vf,τ.commutes] at eq
          exact eq.trans cq.symm
        exact whole_component H hm irr hp h0 τ per cyc u um du uf
    rcases split with unit|full
    · subst u
      simp only [one_mul,coeff_one_zero] at fuv cq
      obtain ⟨S,sub,prod⟩ := ih gl tail v vm dv ⟨q,nq,cq⟩
      exact ⟨S,sub.cons _,prod.trans fuv.symm⟩
    · subst u
      rw [coeff_map] at cq nz
      have nh : H.coeff 0 ≠ 0 := (_root_.map_ne_zero _).mp nz.1
      have vr : v.coeff 0=algebraMap ℚ AlgNums (q/H.coeff 0) := by
        rw [map_div₀,eq_div_iff ((_root_.map_ne_zero _).mpr nh),mul_comm,cq]
      obtain ⟨S,sub,eq⟩ := ih gl tail v vm dv ⟨_,div_ne_zero nq nh,vr⟩
      exact ⟨H::S,sub.cons_cons _,by rw [List.prod_cons,Polynomial.map_mul,eq,fuv]⟩

/-- Every monic complex divisor with nonzero rational constant coefficient
is the product of a sublist of the given rational factors. -/
theorem complex_subproduct (L : List ℚ[X]) (good : ∀ H∈L, PrimeOrLinear H)
    (order : L.Pairwise (fun H P => H.natDegree=1 ∨ P.natDegree<H.natDegree))
    (f : ℂ[X]) (fm : f.Monic) (dv : f ∣ L.prod.map (algebraMap ℚ ℂ))
    (rat : ∃ q : ℚ, q≠0 ∧ f.coeff 0=algebraMap ℚ ℂ q) :
    ∃ S : List ℚ[X], S.Sublist L ∧ S.prod.map (algebraMap ℚ ℂ)=f := by
  classical
  have lm := list_monic L fun P h => (good P h).1
  have lift : f ∈ Polynomial.lifts emb.toRingHom := by
    apply (lifts_iff_coeff_lifts _).mpr
    intro i
    have hi := isIntegral_coeff_of_dvd L.prod f lm fm dv i
    exact ⟨⟨f.coeff i,mem_algebraicClosure_iff.mpr hi.isAlgebraic⟩,rfl⟩
  obtain ⟨F,hF,_,mF⟩ := lifts_and_natDegree_eq_and_monic lift fm
  have tower (P : ℚ[X]) : (P.map (algebraMap ℚ AlgNums)).map emb.toRingHom=P.map (algebraMap ℚ ℂ) := by
    rw [Polynomial.map_map]
    exact congrArg (fun φ : ℚ →+* ℂ => P.map φ) (RingHom.ext_rat _ _)
  have dt : F ∣ L.prod.map (algebraMap ℚ AlgNums) := by
    apply (map_dvd_map emb.toRingHom emb.injective mF).mp
    rwa [hF,tower]
  obtain ⟨q,nq,cq⟩ := rat
  have fc : F.coeff 0=algebraMap ℚ AlgNums q := by
    apply emb.injective
    change emb (F.coeff 0)=emb (algebraMap ℚ AlgNums q)
    rw [emb.commutes,←cq,←hF,coeff_map]
    rfl
  obtain ⟨S,sub,eq⟩ := sublist_of_rational_const L good order F mF dt ⟨q,nq,fc⟩
  exact ⟨S,sub,by rw [←tower,eq,hF]⟩

private theorem integral_unit_const (H : ℤ[X]) (hm : H.Monic) (one : H.coeff 0=1)
    (P : ℚ[X]) (pm : P.Monic) (dv : P∣H.map (algebraMap ℤ ℚ)) :
    P.coeff 0=1 ∨ P.coeff 0= -1 := by
  obtain ⟨Q,prod⟩ := dv
  have qm := pm.of_mul_monic_left (prod ▸ hm.map (algebraMap ℤ ℚ))
  have dQ : Q ∣ H.map (algebraMap ℤ ℚ) := ⟨P,prod.trans (mul_comm _ _)⟩
  obtain ⟨p,hp⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    (isIntegral_coeff_of_dvd H P hm pm ⟨Q,prod⟩ 0)
  obtain ⟨q,hq⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    (isIntegral_coeff_of_dvd H Q hm qm dQ 0)
  have prodc := congrArg (fun f : ℚ[X] => f.coeff 0) prod
  simp only [coeff_map,mul_coeff_zero,one,map_one,←hp,←hq,←map_mul] at prodc
  have ints : p*q=1 := by exact_mod_cast (show ((p*q:ℤ):ℚ)=1 from prodc.symm)
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one ⟨q,ints.symm⟩) with h|h <;> simp [←hp,h]

open Green28 Green28PrimitiveSupport Green28UniformSums Green28PolynomialReduction

/-- Green 28 when the nonlinear rational irreducible factors of the shifted
output mask have pairwise distinct prime degrees and multiplicity one.
Linear factors may repeat. The list orders nonlinear degrees from largest
to smallest. -/
theorem uniform_of_distinct_prime_factors {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q=PMF.uniformOfFinset S ne) (L : List ℚ[X])
    (factorization : L.prod=(outputMask S ne).map (algebraMap ℤ ℚ))
    (degrees : ∀ H∈L, H.Monic ∧ (H.natDegree=1 ∨ Irreducible H ∧ H.natDegree.Prime))
    (order : L.Pairwise (fun H J => H.natDegree=1 ∨ J.natDegree<H.natDegree)) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  obtain ⟨f,g,_,_,_,_,fp,gp,fm,gm,_,_,f0,g0,prod⟩ := mask_factorization ne sum
  let H := outputMask S ne
  have hm : H.Monic := monic_of_injective Int.cast_injective (prod ▸ fm.mul gm)
  have one : H.coeff 0=1 := by
    have c := congrArg (fun p : ℝ[X] => p.coeff 0) prod
    simp only [mul_coeff_zero,f0,g0,mul_one,coeff_map] at c
    exact Int.cast_injective (c.symm.trans (Int.cast_one (R:=ℝ)).symm)
  have good : ∀ T∈L, PrimeOrLinear T := by
    intro T hT
    obtain ⟨tm,kind⟩ := degrees T hT
    refine ⟨tm,kind.imp id fun h => ⟨h.1,h.2,?_⟩⟩
    exact integral_unit_const H hm one T tm (factorization ▸ List.dvd_prod hT)
  let t := algebraMap ℝ ℂ
  have eq : (f.map t)*(g.map t)=L.prod.map (algebraMap ℚ ℂ) := by
    rw [←Polynomial.map_mul,prod,factorization,Polynomial.map_map,Polynomial.map_map]
    exact congrArg (fun φ : ℤ →+* ℂ => H.map φ) (RingHom.ext_int _ _)
  obtain ⟨A,_,sel⟩ := complex_subproduct L good order (f.map t) (fm.map t) ⟨_,eq.symm⟩
    ⟨1,one_ne_zero,by simp only [coeff_map,f0,map_one]⟩
  have rat (i : ℕ) : ∃ q : ℚ, (q:ℝ)=f.coeff i := by
    refine ⟨A.prod.coeff i,?_⟩
    have c := congrArg (fun p : ℂ[X] => p.coeff i) sel
    simp only [coeff_map] at c
    apply Complex.ofReal_injective
    exact (Complex.ofReal_ratCast _).trans c
  have bin := ((fp.mul gp).uniform_iff (fm.mul gm)).mp ⟨S,ne,sum⟩
  obtain ⟨fb,gb⟩ := rational_factor fm gm fp.nonneg gp.nonneg bin rat
  exact ⟨(fp.uniform_iff fm).mpr fb,(gp.uniform_iff gm).mpr gb⟩

#print axioms Green28PrimitiveSupport.mask_factorization
#print axioms split_monic_divisor
#print axioms complex_subproduct
#print axioms uniform_of_distinct_prime_factors

end Green28PrimeFactors
