import research.arxiv.«1104.1579».CunninghamJonesFactorTrace

/-! Complementary modulus restrictions on Jones polynomial factors. -/

namespace CunninghamChain
open Polynomial
open scoped Polynomial

private lemma exact_order_from_size (a M T k : ℕ) (ha : 1<a) (hT : 0<T)
    (hpow : (a:ZMod M)^T=1) (hsize : a^T < (M+1)^k)
    (hgap : ∀ e b : ℕ, T=e*b → e≠T → k ≤ b) : orderOf (a:ZMod M)=T := by
  let e := orderOf (a:ZMod M)
  have he : 0<e := orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨T,hT,hpow⟩)
  obtain ⟨b,hb⟩ := orderOf_dvd_of_pow_eq_one hpow
  by_contra hn
  have hle : e*k ≤ T := hb ▸ Nat.mul_le_mul_left e (hgap e b hb hn)
  have hnat : a^e ≡ 1 [MOD M] := (ZMod.natCast_eq_natCast_iff ..).mp (by simp [e,pow_orderOf_eq_one])
  have hgt := Nat.one_lt_pow he.ne' ha
  have hd := (Nat.modEq_iff_dvd' hgt.le).mp hnat.symm
  have hl := Nat.le_of_dvd (by omega : 0<a^e-1) hd
  have h1 := Nat.pow_le_pow_left (by omega : M+1 ≤ a^e) k
  rw [←pow_mul] at h1
  exact hsize.not_ge (h1.trans (Nat.pow_le_pow_right (by omega) hle))

private lemma odd_constants (t : ℕ) (ho : Odd t) :
    3*((2^t+1)/3)=2^t+1 := by
  have h : 3 ∣ 2^t+1 := by simpa using ho.nat_add_dvd_pow_add_pow 2 1
  simpa [Nat.mul_comm] using Nat.div_mul_cancel h

private lemma index_orders (t : ℕ) (ht : 5≤t) (ho : Odd t) :
    orderOf (2:ZMod (jonesConstant t-1))=t+1 ∧ orderOf (4:ZMod ((2^t+1)/3))=t := by
  let q := (2^t+1)/3
  let M := jonesConstant t-1
  have hq : 3*q=2^t+1 := odd_constants t ho
  have hqp : 9≤q := by have := Nat.pow_le_pow_right (by decide : 0<2) ht; omega
  have hz : M+1=2*q := by change 2*q-1+1=2*q; omega
  have hm : 3*M+1=2^(t+1) := by rw [pow_succ]; omega
  constructor
  · apply exact_order_from_size 2 M (t+1) 2 (by decide) (by omega)
    · simpa using congrArg (fun n : ℕ => (n:ZMod M)) hm.symm
    · rw [←hm]
      nlinarith [show 2 ≤ M by omega]
    · intro e b he hn
      by_contra! hh
      interval_cases b <;> simp_all
  · have hneg : (2:ZMod q)^t = -1 := by
      apply eq_neg_of_add_eq_zero_left
      simpa using congrArg (fun n : ℕ => (n:ZMod q)) hq.symm
    apply exact_order_from_size 4 q t 3 (by decide) (by omega)
    · change (4:ZMod q)^t=1
      rw [show (4:ZMod q)=2^2 by norm_num,←pow_mul,Nat.mul_comm,pow_mul,hneg]
      norm_num
    · rw [show (4:ℕ)=2^2 by decide,←pow_mul,Nat.mul_comm,pow_mul]
      nlinarith [Nat.mul_le_mul_right (q*q) hqp,congrArg (fun x : ℕ => x*x) hq]
    · intro e b he hn
      by_contra! hh
      interval_cases b
      · simp_all
      · simp_all
      · obtain ⟨z,hz⟩ := ho
        omega

/-- Reduce a Jones factor modulo the complementary constant. The complement loses
a factor X, leaving this monic factor as a divisor of X^j−1. -/
theorem jones_factor_complementary_modulus {m j v : ℕ} (hj : 0 < j) (hv : 1 < v)
    {A B : ℤ[X]} (hA : A.Monic) (hAB : A*B=jonesSumPolynomial m j) (hB : B.coeff 0=v) :
    (-1:ZMod v)^(A.natDegree*j)*(A.coeff 0:ZMod v)^j=1 := by
  let : Fact (1<v) := ⟨hv⟩
  let f := Int.castRingHom (ZMod v)
  have h0 := congrArg (fun P : ℤ[X] => P.coeff 0) hAB
  have hm : A.coeff 0*(v:ℤ)=m := by
    simpa [mul_coeff_zero,jonesSumPolynomial,finsetSum_coeff,coeff_X_pow,hB] using h0
  have hm0 : f (m:ℤ)=0 := by rw [←hm,map_mul]; simp [f]
  have geom (n : ℕ) : (X-1)*(jonesSumPolynomial m n).map f=X*(X^n-1) := by
    induction n with
    | zero =>
      have hz : (m:(ZMod v)[X])=0 := by
        simpa only [map_natCast,map_zero] using congrArg (C : ZMod v → (ZMod v)[X]) (show (m:ZMod v)=0 by simpa [f] using hm0)
      simp [jonesSumPolynomial,hz]
    | succ n ih =>
      rw [jonesSumPolynomial_succ,Polynomial.map_add,Polynomial.map_pow,Polynomial.map_X,mul_add,ih]
      ring
  obtain ⟨D,hD⟩ := X_dvd_iff.mpr (show (B.map f).coeff 0=0 by simp [coeff_map,hB,f])
  have hfactor : A.map f*((X-1)*D)=X^j-1 := by
    have H : X*(A.map f*((X-1)*D))=X*(X^j-1) := by
      rw [←geom,←hAB,Polynomial.map_mul,hD]; ring
    ext i
    simpa only [coeff_X_mul] using congrArg (fun P : (ZMod v)[X] => P.coeff (i+1)) H
  let a := A.map f
  let b := (X-1)*D
  have ha : a.Monic := hA.map f
  have hb : b.Monic := ha.of_mul_monic_left (hfactor ▸ by
    simpa using monic_X_pow_sub_C (1:ZMod v) hj.ne')
  have hdeg := congrArg natDegree hfactor
  change (a*b).natDegree=_ at hdeg
  rw [ha.natDegree_mul hb,show (1:(ZMod v)[X])=C 1 by simp,natDegree_X_pow_sub_C] at hdeg
  have hres := resultant_add_mul_right a 1 b a.natDegree j (by omega) le_rfl
  rw [hfactor,show (1:(ZMod v)[X])+(X^j-1)=X^j by ring,resultant_X_pow_right _ _ _ le_rfl,
    resultant_one_right] at hres
  change _ = a.leadingCoeff^j at hres
  simpa [ha.leadingCoeff,a,hA.natDegree_map,coeff_map,f] using hres

private lemma complementary_square {m j u v : ℕ} (hj : 0<j) (hv : 1<v)
    {A B : ℤ[X]} (hA : A.Monic) (hAB : A*B = jonesSumPolynomial m j)
    (hAu : A.coeff 0=u) (hBv : B.coeff 0=v) : ((u:ZMod v)^2)^j=1 := by
  have h := congrArg (fun x : ZMod v => x^2) (jones_factor_complementary_modulus hj hv hA hAB hBv)
  simp only [mul_pow,←pow_mul,Int.cast_natCast,hAu,one_pow] at h
  rw [Nat.mul_comm (A.natDegree*j) 2,pow_mul,neg_one_sq,one_pow,one_mul] at h
  simpa only [←pow_mul,Nat.mul_comm 2 j] using h

private lemma extract_factors {m j : ℕ} (hm : 3 ≤ m) (hj : 0 < j)
    (hred : ¬Irreducible ((jonesSumPolynomial m j).map (Int.castRingHom ℚ))) :
    ∃ A B : ℤ[X], A.Monic ∧ B.Monic ∧ A*B=jonesSumPolynomial m j ∧
      0 < A.natDegree ∧ 0 < B.natDegree ∧ 1 < A.coeff 0 ∧ 1 < B.coeff 0 := by
  by_contra! hn
  apply hred
  obtain ⟨hdeg,hmon⟩ := jonesSumPolynomial_shape m j
  have mon := hmon hj
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast mon.isPrimitive).mp
  apply mon.irreducible_iff_natDegree.mpr
  refine ⟨fun h => by rw [h,natDegree_one] at hdeg; omega,?_⟩
  intro A B hA hB hAB
  by_contra! hd
  have pos (D : ℤ[X]) (hD : D.Monic) (hne : D.natDegree ≠ 0) (hdiv : D ∣ jonesSumPolynomial m j) :
      1 < D.coeff 0 := by
    have h := jones_factor_constant_gt_one (by omega) hD hdiv (Nat.pos_of_ne_zero hne)
    have hp := (jones_factor_constant_congruence hm hj hD (Nat.pos_of_ne_zero hne) hdiv).1
    omega
  have h₁ := pos A hA hd.1 (hAB ▸ dvd_mul_right ..)
  have h₂ := pos B hB hd.2 (hAB ▸ dvd_mul_left ..)
  exact (hn A B hA hB hAB (Nat.pos_of_ne_zero hd.1) (Nat.pos_of_ne_zero hd.2) h₁).not_gt h₂

private lemma constant_product {m j : ℕ} {A B : ℤ[X]} (hAB : A*B=jonesSumPolynomial m j) :
    A.coeff 0*B.coeff 0=m := by
  simpa [jonesSumPolynomial,mul_coeff_zero,finsetSum_coeff,coeff_X_pow] using
    congrArg (fun P : ℤ[X] => P.coeff 0) hAB

private lemma coprime_of_square {u v j : ℕ} (hj : 0 < j) (hs : ((u:ZMod v)^2)^j=1) :
    u.Coprime v := by
  apply (ZMod.isUnit_iff_coprime ..).mp
  exact (isOfFinOrder_iff_pow_eq_one.mpr ⟨2*j,by omega,by simpa [pow_mul] using hs⟩).isUnit

private lemma split_prime_power {u v q : ℕ} (hu : 1<u) (hv : 1<v) (hc : u.Coprime v)
    (h : u*v=2*q) (hq : IsPrimePow q) : u=2 ∨ v=2 := by
  obtain ⟨p,k,hp,hk,rfl⟩ := (isPrimePow_nat_iff q).mp hq
  have hd : p^k ∣ u*v := h ▸ dvd_mul_left ..
  by_cases hpu : p ∣ u
  · have hpv : ¬p ∣ v := fun hh => hp.not_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd hpu hh)
    have hu' := Nat.le_of_dvd (by omega : 0<u) (((hp.coprime_iff_not_dvd.mpr hpv).pow_left k).dvd_of_dvd_mul_right hd)
    right
    nlinarith [Nat.mul_le_mul_right v hu',Nat.pow_pos hp.pos (n:=k)]
  · have hv' := Nat.le_of_dvd (by omega : 0<v) (((hp.coprime_iff_not_dvd.mpr hpu).pow_left k).dvd_of_dvd_mul_left hd)
    left
    nlinarith [Nat.mul_le_mul_left u hv',Nat.pow_pos hp.pos (n:=k)]

/-- A reducible Jones polynomial with constant twice a prime power has a monic
factorization with constants two and that prime power. -/
theorem jones_factor_two_of_prime_power {q j : ℕ} (hq : IsPrimePow q) (hj : 0<j)
    (hred : ¬Irreducible ((jonesSumPolynomial (2*q) j).map (Int.castRingHom ℚ))) :
    ∃ A B : ℤ[X], A.Monic ∧ B.Monic ∧ A*B=jonesSumPolynomial (2*q) j ∧
      0<A.natDegree ∧ A.coeff 0=2 ∧ B.coeff 0=q := by
  have hq2 := hq.one_lt
  obtain ⟨A,B,ha,hb,hab,da,db,ca,cb⟩ := extract_factors (by omega : 3≤2*q) hj hred
  let u := (A.coeff 0).toNat
  let v := (B.coeff 0).toNat
  have au : A.coeff 0=(u:ℤ) := by dsimp [u]; omega
  have bv : B.coeff 0=(v:ℤ) := by dsimp [v]; omega
  have huv' := constant_product hab
  rw [au,bv] at huv'
  have huv : u*v=2*q := by exact_mod_cast huv'
  have hc := coprime_of_square hj (complementary_square hj (by omega) ha hab au bv)
  rcases split_prime_power (by omega) (by omega) hc huv hq with h|h
  · refine ⟨A,B,ha,hb,hab,da,by omega,?_⟩
    rw [h] at huv; omega
  · refine ⟨B,A,hb,ha,mul_comm A B ▸ hab,db,by omega,?_⟩
    rw [h] at huv; omega

/-- At every odd parameter t ≥ 5, a monic factor with constant two forces
the degree into the single class t modulo t(t+1). -/
theorem jones_constant_two_degree_class {t j : ℕ} (ht : 5≤t) (ho : Odd t) (hj : 0<j)
    {A : ℤ[X]} (hA : A.Monic) (hdiv : A ∣ jonesSumPolynomial (jonesConstant t) j)
    (hAu : A.coeff 0=2) : j ≡ t [MOD t*(t+1)] := by
  let q := (2^t+1)/3
  have hq : 9≤q := by
    have he := odd_constants t ho
    have := Nat.pow_le_pow_right (by decide : 0<2) ht
    dsimp [q]; omega
  have hm : jonesConstant t=2*q := rfl
  have hdeg : 0<A.natDegree := by
    by_contra! h
    have h1 := hA.natDegree_eq_zero.mp (by omega)
    simp [h1] at hAu
  obtain ⟨B,hB⟩ := hdiv
  have hBv : B.coeff 0=(q:ℤ) := by
    have h := constant_product hB.symm
    rw [hAu,hm,Nat.cast_mul,Nat.cast_ofNat] at h
    omega
  obtain ⟨hord₂,hord₄⟩ := index_orders t ht ho
  have mod₂ := (jones_factor_constant_congruence (by omega) hj hA hdeg ⟨B,hB⟩).2
  rw [hAu] at mod₂
  have h₂ : t+1 ∣ j+1 := hord₂ ▸ orderOf_dvd_of_pow_eq_one (by simpa using mod₂)
  have mod₄ := complementary_square (u:=2) hj (by omega : 1<q) hA hB.symm (by exact_mod_cast hAu) hBv
  simp only [Nat.cast_ofNat] at mod₄
  rw [show (2:ZMod q)^2=4 by norm_num] at mod₄
  have h₄ : t ∣ j := hord₄ ▸ orderOf_dvd_of_pow_eq_one mod₄
  have hleft : j ≡ t [MOD t] := (Nat.modEq_zero_iff_dvd.mpr h₄).trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl).symm
  have hright : j+1 ≡ t+1 [MOD t+1] := (Nat.modEq_zero_iff_dvd.mpr h₂).trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl).symm
  exact (Nat.modEq_and_modEq_iff_modEq_mul (by simp : t.Coprime (t+1))).mp ⟨hleft,Nat.ModEq.add_right_cancel' 1 hright⟩

/-- Reducibility for a Jones parameter with prime-power odd part forces the same
degree class as a constant-two factor. -/
theorem jones_prime_power_part_degree_class {t j : ℕ} (ht : 5≤t) (ho : Odd t)
    (hq : IsPrimePow ((2^t+1)/3)) (hj : 0<j)
    (hred : ¬Irreducible ((jonesSumPolynomial (jonesConstant t) j).map (Int.castRingHom ℚ))) :
    j ≡ t [MOD t*(t+1)] := by
  obtain ⟨A,B,hA,_,hAB,_,hAu,_⟩ := jones_factor_two_of_prime_power hq hj hred
  exact jones_constant_two_degree_class ht ho hj hA ⟨B,hAB.symm⟩ hAu

private lemma exceptional_irreducibility {t : ℕ} (ht : 3≤t) (ho : Odd t) :
    ¬Irreducible ((jonesSumPolynomial (jonesConstant t) t).map (Int.castRingHom ℚ)) := by
  intro h
  have hr := (jones_rational_root_iff t t ht ho (by omega) (by nlinarith) (-2)).mpr ⟨rfl,rfl⟩
  have he := natDegree_eq_of_degree_eq_some (degree_eq_one_of_irreducible_of_root h hr)
  rw [natDegree_map_eq_of_injective Int.cast_injective,(jonesSumPolynomial_shape _ _).1] at he
  change t=1 at he
  omega

/-- The predicted classification up to the second possible degree in this class,
and throughout the earlier exponential bound, now assumes only a prime-power odd part. -/
theorem jones_prime_power_part_range (t j : ℕ) (ht : 5≤t) (ho : Odd t)
    (hp : IsPrimePow ((2^t+1)/3)) (hj : 0<j)
    (hbound : j<t+t*(t+1) ∨ j^3*2^(2*(t+1)) ≤ (jonesConstant t)^3) :
    Irreducible ((jonesSumPolynomial (jonesConstant t) j).map (Int.castRingHom ℚ)) ↔ j≠t := by
  constructor
  · rintro h h'
    exact exceptional_irreducibility (by omega) ho (h' ▸ h)
  · intro hne
    by_contra hred
    have hm := jones_prime_power_part_degree_class ht ho hp hj hred
    have hmod : t < t*(t+1) := by nlinarith
    rcases hbound with hsmall|hcut
    · have h₁ : t ≤ j := by
        by_contra! hl
        exact hne (hm.eq_of_lt_of_lt (hl.trans hmod) hmod)
      obtain ⟨k,hk⟩ := (Nat.modEq_iff_exists_eq_add h₁).mp hm.symm
      rcases k with _|k
      · simp [hk] at hne
      · rw [Nat.mul_succ] at hk; omega
    · have ht1 := (Nat.modEq_and_modEq_iff_modEq_mul (by simp : t.Coprime (t+1))).mpr hm
      have hD : t+1 ∣ j+1 := Nat.modEq_zero_iff_dvd.mp (ht1.2.add_right 1 |>.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl))
      obtain ⟨k,hk⟩ := hD
      have hk2 : 2≤k := by rcases k with _|(_|k) <;> simp_all
      have h4 : 4*j ≤ jonesConstant t := by
        apply (Nat.pow_le_pow_iff_left (by decide : (3:ℕ)≠0)).mp
        rw [mul_pow,Nat.mul_comm (4^3)]
        exact (Nat.mul_le_mul_left _ (show 2^6 ≤ 2^(2*(t+1)) from
          Nat.pow_le_pow_right (by decide) (by omega))).trans hcut
      obtain ⟨A,B,hA,_,hAB,hd,hAu,_⟩ := jones_factor_two_of_prime_power hp hj hred
      have hk4 : 4*k ≤ j+1 := hk ▸ Nat.mul_le_mul_right k (by omega : 4≤t+1)
      obtain ⟨hdegree,hsize⟩ := jones_constant_two_degree_bounds ho (by omega) hk2 (by omega) hk hA hd ⟨B,hAB.symm⟩ hAu
      let e := A.natDegree
      have H : j^(3*e)*2^((2*(t+1))*e) ≤ j^(3*e)*2^(j*3) := by
        calc j^(3*e)*2^((2*(t+1))*e) = (j^3*2^(2*(t+1)))^e := by rw [mul_pow,pow_mul,pow_mul]
             _ ≤ ((jonesConstant t)^3)^e := Nat.pow_le_pow_left hcut _
             _ = ((jonesConstant t)^e)^3 := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
             _ ≤ (j^e*2^j)^3 := Nat.pow_le_pow_left hsize _
             _ = _ := by rw [mul_pow,←pow_mul,←pow_mul,Nat.mul_comm e 3]
      have E := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
        (Nat.le_of_mul_le_mul_left H (Nat.pow_pos hj))
      change 3*k ≤ 2*e at hdegree
      nlinarith only [E,hk,Nat.mul_le_mul_left (t+1) hdegree]

private lemma specific_order {R : Type*} [Monoid R] {x : R} {n : ℕ} (hn : 0<n) (hx : x^n=1)
    (h : ∀ i : Fin n, 0 < i.val → x ^ i.val ≠ 1) : orderOf x=n :=
  (orderOf_eq_iff hn).mpr ⟨hx,fun i hi => h ⟨i,hi⟩⟩

/-- For the composite odd part at t=9, at most four residue classes modulo
90 can have a reducible polynomial. -/
theorem jones_nine_complementary_classes (j : ℕ) (hj : 0<j)
    (hred : ¬Irreducible ((jonesSumPolynomial 342 j).map (Int.castRingHom ℚ))) :
    j%90=9 ∨ 30 ∣ j+1 := by
  obtain ⟨A,B,ha,hb,hab,da,db,ca,cb⟩ := extract_factors (by decide : 3≤342) hj hred
  have check (A B : ℤ[X]) (ha : A.Monic) (hAB : A*B=jonesSumPolynomial 342 j) (hd : 0<A.natDegree)
      (ca : 1<A.coeff 0) (cb : 1<B.coeff 0) (hle : A.coeff 0≤B.coeff 0) :
      j%90=9 ∨ 30∣j+1 := by
    let u := (A.coeff 0).toNat
    let v := (B.coeff 0).toNat
    have au : A.coeff 0=(u:ℤ) := by dsimp [u]; omega
    have bv : B.coeff 0=(v:ℤ) := by dsimp [v]; omega
    have hprod := constant_product hAB
    rw [au,bv] at hprod
    have prod : u*v=342 := by exact_mod_cast hprod
    have hsq := complementary_square hj (by omega) ha hAB au bv
    have hcop := coprime_of_square hj hsq
    have hu : u<19 := by nlinarith [Nat.mul_le_mul_left u (by omega : u≤v),sq_nonneg ((u:ℤ)-19)]
    have htab : ∀ i : Fin 19, 1 < i.val → i.val ∣ 342 → i.val.Coprime (342/i.val) →
        i.val=2 ∨ i.val=9 ∨ i.val=18 := by decide
    have hu1 : 1 < u := by omega
    have hcases := htab ⟨u,hu⟩ hu1 (prod ▸ dvd_mul_right ..)
      (by rwa [←prod,Nat.mul_div_cancel_left _ (by omega)])
    have hm := (jones_factor_constant_congruence (by decide) hj ha hd (hAB ▸ dvd_mul_right ..)).2
    rcases hcases with h|h|h <;> change u=_ at h
    · left
      have hAu : A.coeff 0=2 := by omega
      exact jones_constant_two_degree_class (by decide : 5≤9) (by decide) hj ha ⟨B,hAB.symm⟩ hAu
    · have hv : v=38 := by rw [h] at prod; omega
      have h1 : (9:ZMod 341)^(j+1)=1 := by simpa [au,h] using hm
      have h2 : (81:ZMod 38)^j=1 := by
        rw [h,hv,show ((9:ℕ):ZMod 38)^2=81 by decide] at hsq
        exact hsq
      have o1 : orderOf (9:ZMod 341)=15 := specific_order (by decide) (by decide) (by decide)
      have o2 : orderOf (81:ZMod 38)=9 := specific_order (by decide) (by decide) (by decide)
      have ha' := o1 ▸ orderOf_dvd_of_pow_eq_one h1
      have hb' := o2 ▸ orderOf_dvd_of_pow_eq_one h2
      omega
    · right
      have h1 : (18:ZMod 341)^(j+1)=1 := by simpa [au,h] using hm
      have o1 : orderOf (18:ZMod 341)=30 := specific_order (by decide) (by decide) (by decide)
      exact o1 ▸ orderOf_dvd_of_pow_eq_one h1
  rcases le_total (A.coeff 0) (B.coeff 0) with h|h
  · exact check A B ha hab da ca cb h
  · exact check B A hb (mul_comm A B ▸ hab) db cb ca h

#print axioms jones_factor_two_of_prime_power
#print axioms jones_factor_complementary_modulus
#print axioms jones_constant_two_degree_class
#print axioms jones_prime_power_part_degree_class
#print axioms jones_prime_power_part_range
#print axioms jones_nine_complementary_classes

end CunninghamChain
