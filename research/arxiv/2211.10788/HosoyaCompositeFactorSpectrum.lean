import HosoyaFactorDegrees
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Extension

/-! # Frobenius degrees at arbitrary upper Hosoya progression steps -/

namespace Arxiv.«2211.10788»
open Polynomial
open scoped Polynomial

private theorem frobenius_period_iff {p : ℕ} [Fact p.Prime] {K : Type*} [Field K]
    [Algebra (ZMod p) K] {g : (ZMod p)[X]} (hg : Irreducible g) {x : K}
    (hx : g.aeval x=0) (e : ℕ) : g.natDegree ∣ e ↔ x^(p^e)=x := by
  rw [hg.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X,←hg.dvd_iff_aeval_eq_zero hx]
  simp [Nat.card_eq_fintype_card,sub_eq_zero]

private theorem coordinate_finite_order {p : ℕ} [Fact p.Prime] {K : Type*} [Field K]
    [Algebra (ZMod p) K] {w : K} (hi : IsIntegral (ZMod p) w) (hw : w≠0) :
    0 < orderOf w := by
  let g := minpoly (ZMod p) w
  have hg : Irreducible g := minpoly.irreducible hi
  have hpow := (frobenius_period_iff hg (minpoly.aeval (ZMod p) w) g.natDegree).mp dvd_rfl
  have hne := one_lt_pow₀ (Fact.out : p.Prime).one_lt hg.natDegree_pos.ne'
  apply orderOf_pos_iff.mpr
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨p^g.natDegree-1,by omega,?_⟩
  apply mul_right_cancel₀ hw
  rw [one_mul,←pow_succ,Nat.sub_add_cancel (by omega),hpow]

/-- The fractional linear coordinate takes an affine zero to the prescribed power
fiber. The missing coordinate 1 represents the point at infinity. -/
theorem upperIndexForm_affine_fiber {K : Type*} [Field K] {a b x : K} {r d : ℕ}
    (ha : a^2=a+1) (hb : b^2=b+1) (hab : a≠b)
    (hA : (3+a)*a^r≠0) (hd : 0<d) :
    upperIndexForm x 1 d r=0 ↔ x+b≠0 ∧
      ((x+a)/(x+b))^d=((3+b)*b^r)/((3+a)*a^r) := by
  have form : upperIndexForm x 1 d r=0 ↔
      ((3+a)*a^r)*(x+a)^d=((3+b)*b^r)*(x+b)^d := by
    rw [←mul_right_inj' (sub_ne_zero.mpr hab),mul_zero,upper_form_conjugates ha hb]
    simp [sub_eq_zero]
  rw [form]
  constructor
  · intro he
    have hx : x+b≠0 := by
      intro hz
      have hn : x+a≠0 := fun h => hab (add_left_cancel (h.trans hz.symm))
      exact mul_ne_zero hA (pow_ne_zero _ hn) (by simpa [hz,zero_pow hd.ne'] using he)
    refine ⟨hx,?_⟩
    rw [div_pow,div_eq_div_iff (pow_ne_zero _ hx) hA]
    linear_combination he
  · rintro ⟨hx,he⟩
    rw [div_pow,div_eq_div_iff (pow_ne_zero _ hx) hA] at he
    linear_combination he

/-- For every affine zero of the canonical upper polynomial, its coordinate
order is greater than one, and the power map fixes its precise gcd with the step. -/
theorem upperIndexPolynomial_root_order {p r d : ℕ} [Fact p.Prime]
    {a b x : AlgebraicClosure (ZMod p)} (ha : a^2=a+1) (hb : b^2=b+1)
    (hab : a≠b) (hA : (3+a)*a^r≠0) (hB : (3+b)*b^r≠0) (hd : 0<d)
    (hx : ((upperIndexPolynomial r d).map (Int.castRingHom (ZMod p))).aeval x=0) :
    let w := (x+a)/(x+b)
    1 < orderOf w ∧ orderOf w / (orderOf w).gcd d =
      orderOf (((3+b)*b^r)/((3+a)*a^r)) := by
  rw [upperIndexPolynomial_aeval] at hx
  obtain ⟨hxb,hw⟩ := (upperIndexForm_affine_fiber ha hb hab hA hd).mp hx
  let w := (x+a)/(x+b)
  change w^d=_ at hw
  have hn : w≠0 := by
    intro hz
    exact div_ne_zero hB hA (by simpa [hz,zero_pow hd.ne'] using hw.symm)
  have ho := coordinate_finite_order (p:=p) (Algebra.IsIntegral.isIntegral w) hn
  have he : orderOf w≠1 := by
    intro h
    exact hab (add_left_cancel ((div_eq_one_iff_eq hxb).mp (orderOf_eq_one_iff.mp h)))
  exact ⟨by change 1 < orderOf w; omega,by rw [←hw,orderOf_pow' w hd.ne']⟩

private theorem exists_power_preimage_of_order {K : Type*} [Field K] {t d : ℕ}
    [HasEnoughRootsOfUnity K t] (ht : 0<t) (hd : 0<d) {C : K}
    (hm : t/t.gcd d=orderOf C) : ∃ w : K, orderOf w=t ∧ w^d=C := by
  let m := orderOf C
  have hmdiv : m ∣ t := by change orderOf C ∣ t; rw [←hm]; exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left t d)
  let : NeZero t := ⟨ht.ne'⟩
  let : NeZero m := ⟨(Nat.pos_of_dvd_of_pos hmdiv ht).ne'⟩
  obtain ⟨z,hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K t
  have hzd : IsPrimitiveRoot (z^d) m := by
    apply IsPrimitiveRoot.iff_orderOf.mpr
    rw [orderOf_pow' z hd.ne',←hz.eq_orderOf]
    exact hm
  obtain ⟨j,_,hj,hjC⟩ := hzd.isPrimitiveRoot_iff.mp (IsPrimitiveRoot.orderOf C)
  obtain ⟨u,hu⟩ := ZMod.unitsMap_surjective hmdiv (ZMod.unitOfCoprime j hj)
  let k := (u : ZMod t).val
  have hmod : k ≡ j [MOD m] := by
    rw [←ZMod.natCast_eq_natCast_iff]
    have hh := congrArg (fun v : (ZMod m)ˣ => (v : ZMod m)) hu
    calc
      (k:ZMod m) = ZMod.castHom hmdiv (ZMod m) (u:ZMod t) := by
        conv_rhs => rw [←ZMod.natCast_zmod_val (u:ZMod t),map_natCast]
      _ = (j:ZMod m) := by simpa only [ZMod.unitsMap_def,Units.coe_map,MonoidHom.coe_coe,
        ZMod.coe_unitOfCoprime] using hh
  refine ⟨z^k,(hz.pow_of_coprime k (ZMod.val_coe_unit_coprime u)).eq_orderOf.symm,?_⟩
  rw [←pow_mul,mul_comm,pow_mul,←hjC]
  exact pow_eq_pow_of_modEq hmod hzd.pow_eq_one

/-- The degree of a factor through any affine zero is the multiplicative
order of the signed Frobenius residue modulo the order of that zero's coordinate. -/
theorem upperIndexPolynomial_affine_factor_degree {p r d : ℕ} [Fact p.Prime]
    (hp5 : p≠5) {a b x : AlgebraicClosure (ZMod p)} (ha : a^2=a+1) (hb : b^2=b+1)
    (hba : b=1-a) (hab : a≠b) (hA : (3+a)*a^r≠0) (hB : (3+b)*b^r≠0)
    (hd : 0<d) {g : (ZMod p)[X]} (hg : Irreducible g) (hx : g.aeval x=0)
    (hdiv : g ∣ (upperIndexPolynomial r d).map (Int.castRingHom (ZMod p))) :
    let t := orderOf ((x+a)/(x+b))
    g.natDegree=orderOf (if p%5=2 ∨ p%5=3 then -(p:ZMod t) else (p:ZMod t)) := by
  have hroot := (hg.dvd_iff_aeval_eq_zero hx).mpr hdiv
  have ho := (upperIndexPolynomial_root_order ha hb hab hA hB hd hroot).1
  rw [upperIndexPolynomial_aeval] at hroot
  obtain ⟨hxb,hw⟩ := (upperIndexForm_affine_fiber ha hb hab hA hd).mp hroot
  have hxa : x+a≠0 := by
    intro he
    exact div_ne_zero hB hA (by simpa [he,zero_pow hd.ne'] using hw.symm)
  exact upper_ratio_frobenius_degree hp5 ha hba hab 1 0 hg hx (by simp) (by simp) hxb
    (by omega : 0 < orderOf ((x+a)/(x+b))) (by simp) hxa

private theorem factor_degree_spectrum_at_pair {p r d n : ℕ} [Fact p.Prime]
    (hp5 : p≠5) {a b : AlgebraicClosure (ZMod p)} (ha : a^2=a+1) (hb : b^2=b+1)
    (hba : b=1-a) (hab : a≠b) (hA : (3+a)*a^r≠0) (hB : (3+b)*b^r≠0) (hd : 0<d) :
    (∃ g : (ZMod p)[X], Irreducible g ∧ g ∣ (upperIndexPolynomial r d).map (Int.castRingHom (ZMod p))
      ∧ g.natDegree=n) ↔ ∃ t : ℕ, 1<t ∧ ¬p ∣ t ∧ t/t.gcd d=orderOf (((3+b)*b^r)/((3+a)*a^r))
      ∧ n=orderOf (if p%5=2 ∨ p%5=3 then -(p:ZMod t) else (p:ZMod t)) := by
  let K := AlgebraicClosure (ZMod p)
  let incl := algebraMap (ZMod p) K
  constructor
  · rintro ⟨g,hg,hdiv,rfl⟩
    have hgpos : 0 < (g.map incl).degree := by
      rw [degree_eq_natDegree (map_ne_zero hg.ne_zero),natDegree_map]
      exact_mod_cast hg.natDegree_pos
    obtain ⟨x,hx₀⟩ := IsAlgClosed.exists_root (g.map incl) hgpos.ne'
    have hx : g.aeval x=0 := by simpa [IsRoot,incl,eval_map_algebraMap] using hx₀
    let w := (x+a)/(x+b)
    have hh := upperIndexPolynomial_root_order ha hb hab hA hB hd
      ((hg.dvd_iff_aeval_eq_zero hx).mpr hdiv)
    change 1<orderOf w ∧ _ at hh
    let : NeZero (orderOf w) := ⟨by omega⟩
    have nz := (IsPrimitiveRoot.orderOf w).neZero'
    refine ⟨orderOf w,hh.1,(CharP.cast_eq_zero_iff K p _).not.mp nz.out,hh.2,?_⟩
    exact upperIndexPolynomial_affine_factor_degree hp5 ha hb hba hab hA hB hd hg hx hdiv
  · rintro ⟨t,ht,hpt,hm,rfl⟩
    let : NeZero (t : ZMod p) := ⟨(ZMod.natCast_eq_zero_iff t p).not.mpr hpt⟩
    obtain ⟨w,hw,hwd⟩ := exists_power_preimage_of_order (by omega : 0<t) hd hm
    have hw1 : w≠1 := fun he => (by omega : t≠1) (hw.symm.trans (orderOf_eq_one_iff.mpr he))
    let x := (a-w*b)/(w-1)
    have hxb : x+b=(a-b)/(w-1) := by dsimp [x]; field_simp; ring
    have hn : x+b≠0 := hxb ▸ div_ne_zero (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hw1)
    have ratio : (x+a)/(x+b)=w := by
      apply (div_eq_iff hn).mpr
      dsimp [x]
      field_simp
      ring
    have hx : ((upperIndexPolynomial r d).map (Int.castRingHom (ZMod p))).aeval x=0 := by
      rw [upperIndexPolynomial_aeval,upperIndexForm_affine_fiber ha hb hab hA hd,ratio]
      exact ⟨hn,hwd⟩
    let g := minpoly (ZMod p) x
    have hg : Irreducible g := minpoly.irreducible (Algebra.IsIntegral.isIntegral x)
    have hmin : g.aeval x=0 := minpoly.aeval _ _
    have hdiv := (hg.dvd_iff_aeval_eq_zero hmin).mp hx
    refine ⟨g,hg,hdiv,?_⟩
    apply (upperIndexPolynomial_affine_factor_degree hp5 ha hb hba hab hA hB hd hg hmin hdiv).trans
    exact congrArg (fun k => orderOf (if p%5=2 ∨ p%5=3 then -(p:ZMod k) else (p:ZMod k)))
      ((congrArg orderOf ratio).trans hw)

private theorem coefficient_power_iff {p r : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [Algebra (ZMod p) K] {a b : K}
    (ha : a^2=a+1) (hb : b^2=b+1) (hab : a≠b) (hA : (3+a)*a^r≠0) (k : ℕ) :
    (((3+b)*b^r)/((3+a)*a^r))^k=1 ↔ (upperIndexStart (ZMod p) r ^ k).im=0 := by
  let incl := algebraMap (ZMod p) K
  let z := upperIndexStart (ZMod p) r ^ k
  have at_root {c : K} (hc : c^2=c+1) : ((3+c)*c^r)^k=incl z.re+incl z.im*c := by
    let ev : QuadraticAlgebra (ZMod p) 1 1 →ₐ[ZMod p] K :=
      QuadraticAlgebra.lift ⟨c,by simpa [pow_two,add_comm] using hc⟩
    have eval (v : QuadraticAlgebra (ZMod p) 1 1) :
        ev v=incl v.re+incl v.im*c := by
      change v.re • (1:K)+v.im • c=_
      simp [Algebra.smul_def,incl]
    have four : incl 4=4 := map_natCast incl 4
    have start (n : ℕ) : ev (upperIndexStart (ZMod p) n)=(3+c)*c^n := by
      induction n with
      | zero => simp [upperIndexStart,eval,lucas_fibonacci_sum_zero,lucas_fibonacci_sum_one,four]; ring
      | succ n ih =>
        rw [pow_succ,←mul_assoc,←ih,eval,eval]
        simp only [upperIndexStart,show n+1+1=n+2 by omega,lucas_fibonacci_sum_recurrence,
          Nat.cast_add,map_sub,map_add,map_natCast]
        linear_combination -(lucasFibonacciSum n : K)*hc
    rw [←start,←map_pow,eval]
  rw [div_pow,div_eq_one_iff_eq (pow_ne_zero _ hA),at_root hb,at_root ha,add_right_inj,
    mul_eq_mul_left_iff]
  simp [hab.symm,incl,z]

private theorem parameter_order_bound {p r : ℕ} [Fact p.Prime] (hp5 : p≠5)
    {K : Type*} [Field K] [Algebra (ZMod p) K] [CharP K p] {a b : K}
    (ha : a^2=a+1) (hba : b=1-a) (hA : (3+a)*a^r≠0) (hB : (3+b)*b^r≠0) :
    orderOf (((3+b)*b^r)/((3+a)*a^r)) ≤ p+1 := by
  let C := ((3+b)*b^r)/((3+a)*a^r)
  have hC : C≠0 := div_ne_zero hB hA
  have three : frobenius K p 3=3 := map_natCast _ 3
  have hf := frobenius_fibonacci_root hp5 ha hba
  by_cases h : p%5=2 ∨ p%5=3
  · rw [if_pos h] at hf
    have hf' : frobenius K p b=a := by rw [hba,map_sub,map_one,hf,hba]; ring
    have hc : C^p=C⁻¹ := by
      change frobenius K p C=C⁻¹
      simp [C,hf,hf',three]
    exact Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one (by
      rw [pow_succ,hc,inv_mul_cancel₀ hC] : C^(p+1)=1))
  · rw [if_neg h] at hf
    have hf' : frobenius K p b=b := by rw [hba,map_sub,map_one,hf]
    have hc : C^p=C := by change frobenius K p C=C; simp [C,hf,hf',three]
    have hp := (Fact.out : p.Prime).one_lt
    have he : C^(p-1)=1 := by
      apply mul_right_cancel₀ hC
      rw [←pow_succ,Nat.sub_add_cancel (by omega),one_mul,hc]
    exact (Nat.le_of_dvd (by omega : 0<p-1) (orderOf_dvd_of_pow_eq_one he)).trans (by omega)

/-- For every positive progression step, a bounded test in the base quadratic
algebra gives all degrees of irreducible factors at ordinary primes. It covers
inseparable steps and a vanishing leading coefficient. -/
theorem upperIndexPolynomial_factor_degree_spectrum {p : ℕ} [Fact p.Prime]
    (hp5 : p≠5) (hp11 : p≠11) (r d n : ℕ) (hd : 0<d) :
    (∃ g : (ZMod p)[X], Irreducible g ∧ g ∣ (upperIndexPolynomial r d).map (Int.castRingHom (ZMod p))
      ∧ g.natDegree=n) ↔ ∃ t : ℕ, 1<t ∧ t≤d*(p+1) ∧ ¬p ∣ t ∧
      (upperIndexStart (ZMod p) r ^ (t/t.gcd d)).im=0 ∧
      (∀ j, j<t/t.gcd d → 0<j → (upperIndexStart (ZMod p) r ^ j).im≠0) ∧
      n=orderOf (if p%5=2 ∨ p%5=3 then -(p:ZMod t) else (p:ZMod t)) := by
  let K := AlgebraicClosure (ZMod p)
  have nz (q : ℕ) (hq : q.Prime) (hne : p≠q) : (q:K)≠0 := fun he =>
    hne ((Nat.prime_dvd_prime_iff_eq Fact.out hq).mp ((CharP.cast_eq_zero_iff K p q).mp he))
  obtain ⟨a,b,ha,hb,hba,hab,hA,hB⟩ := upperIndexForm_conjugate_data K
    (nz 5 (by decide) hp5) (nz 11 (by decide) hp11) r
  let C := ((3+b)*b^r)/((3+a)*a^r)
  have test := coefficient_power_iff (p:=p) ha hb hab hA
  have cap := parameter_order_bound hp5 ha hba hA hB
  rw [factor_degree_spectrum_at_pair hp5 ha hb hba hab hA hB hd]
  have exact_order (t : ℕ) (ht : 1<t) :
      t/t.gcd d=orderOf C ↔ (upperIndexStart (ZMod p) r ^ (t/t.gcd d)).im=0 ∧
        ∀ j, j<t/t.gcd d → 0<j → (upperIndexStart (ZMod p) r ^ j).im≠0 := by
    have hdiv := Nat.gcd_dvd_left t d
    have hg := Nat.gcd_pos_of_pos_left d (by omega : 0<t)
    have hpos := Nat.div_pos (Nat.le_of_dvd (by omega) hdiv) hg
    rw [eq_comm,orderOf_eq_iff hpos]
    simp only [C,ne_eq,test]
  constructor
  · rintro ⟨t,ht,hp,hm,hn⟩
    obtain ⟨he,hl⟩ := (exact_order t ht).mp hm
    refine ⟨t,ht,?_,hp,he,hl,hn⟩
    calc
      t = (t.gcd d)*(t/t.gcd d) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left t d)).symm
      _ ≤ d*(p+1) := Nat.mul_le_mul (Nat.gcd_le_right _ hd) (hm.le.trans cap)
  · rintro ⟨t,ht,_,hp,he,hl,hn⟩
    exact ⟨t,ht,hp,(exact_order t ht).mpr ⟨he,hl⟩,hn⟩

#print axioms upperIndexPolynomial_factor_degree_spectrum
#print axioms upperIndexPolynomial_affine_factor_degree
#print axioms upperIndexForm_affine_fiber
#print axioms upperIndexPolynomial_root_order

end Arxiv.«2211.10788»
