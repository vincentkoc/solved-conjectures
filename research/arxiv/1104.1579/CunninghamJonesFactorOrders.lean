import research.arxiv.«1104.1579».CunninghamJonesLargeDegree
/-! Degree obstructions for factors of Jones polynomials. -/

namespace CunninghamChain
open Polynomial
open scoped Polynomial
/-- The resultant with X^N can be computed from the constant coefficient or from X^N ≡ 1. -/
private lemma unity_factor_constant {R : Type*} [CommRing R] [Nontrivial R]
    (a b : R[X]) (ha : a.Monic) (hb : b.Monic) (N : ℕ) (h : a*b = X^N-1) :
    (-1:R)^(a.natDegree*N)*a.coeff 0^N = 1 := by
  have hd := congrArg natDegree h
  rw [ha.natDegree_mul hb] at hd
  rw [show (1:R[X])=C 1 by simp,natDegree_X_pow_sub_C] at hd
  have hr := resultant_add_mul_right a 1 b a.natDegree N (by omega) le_rfl
  rw [h,show (1:R[X])+(X^N-1)=X^N by ring,resultant_X_pow_right _ _ _ le_rfl,resultant_one_right] at hr
  change _ = a.leadingCoeff^N at hr
  simpa [ha.leadingCoeff] using hr

private lemma geom_map {R : Type*} [CommRing R] (f : ℤ →+* R) (m j : ℕ) :
    (X-1)*(jonesSumPolynomial m j).map f = X^(j+1)+(C (f m)-1)*X-C (f m) := by
  induction j with
  | zero => simp [jonesSumPolynomial]; ring
  | succ j ih =>
    rw [jonesSumPolynomial_succ,Polynomial.map_add,Polynomial.map_pow,Polynomial.map_X,mul_add,ih]
    ring

private lemma factor_signed_constant {m j : ℕ} (hm : 3 ≤ m) (hj : 0 < j)
    {a : ℤ[X]} (ha : a.Monic) (hdiv : a ∣ jonesSumPolynomial m j) :
    (-1:ZMod (m-1))^(a.natDegree*(j+1))*(a.coeff 0 : ZMod (m-1))^(j+1) = 1 := by
  have hlarge : 1 < m-1 := by omega
  let : Fact (1 < m-1) := ⟨hlarge⟩
  let f := Int.castRingHom (ZMod (m-1))
  have hm1 : f (m:ℤ) = 1 := by
    change ((m:ℤ):ZMod (m-1))=1
    simp only [Int.cast_natCast]
    calc (m:ZMod (m-1)) = ((m-1:ℕ):ZMod (m-1))+1 := by
           simpa only [Nat.cast_add,Nat.cast_one] using congrArg (fun n : ℕ => (n : ZMod (m-1))) (show m=m-1+1 by omega)
         _ = 1 := by simp
  obtain ⟨b,hb⟩ := hdiv
  have hbm := ha.of_mul_monic_left (hb ▸ (jonesSumPolynomial_shape m j).2 hj)
  have hgeom := geom_map f m j
  rw [hm1,hb,Polynomial.map_mul] at hgeom
  have hprod : a.map f*((X-1)*b.map f) = X^(j+1)-1 := by
    rw [mul_left_comm]
    simpa [mul_assoc] using hgeom
  have hmon : ((X-1)*(b.map f)).Monic := by
    simpa using (monic_X_sub_C (1:ZMod (m-1))).mul (hbm.map f)
  simpa [ha.natDegree_map,coeff_map,f] using unity_factor_constant _ _ (ha.map f) hmon _ hprod

private lemma real_jones_positive (m j : ℕ) (hm : 0 < m) (z : ℝ) (hz : 0 ≤ z) :
    0 < ((jonesSumPolynomial m j).map (Int.castRingHom ℝ)).eval z := by
  simp only [jonesSumPolynomial,Polynomial.map_add,map_C,Polynomial.map_sum,Polynomial.map_pow,
    Polynomial.map_X,eval_add,eval_C,eval_finsetSum,eval_pow,eval_X,Int.coe_castRingHom,Int.cast_natCast]
  positivity

private lemma monic_factor_positive {m j : ℕ} (hm : 0 < m) {a : ℤ[X]} (ha : a.Monic)
    (hd : 0 < a.natDegree) (hdiv : a ∣ jonesSumPolynomial m j) : 0 < a.coeff 0 := by
  let A := a.map (Int.castRingHom ℝ)
  have hmon := ha.map (Int.castRingHom ℝ)
  have hdeg : 0 < A.degree := natDegree_pos_iff_degree_pos.mp (by simpa [A,ha.natDegree_map] using hd)
  have he := A.tendsto_atTop_of_leadingCoeff_nonneg hdeg (le_of_lt (by rw [hmon.leadingCoeff]; exact zero_lt_one))
  obtain ⟨z,hz,hz'⟩ := ((Filter.eventually_ge_atTop (0:ℝ)).and (he.eventually_ge_atTop 0)).exists
  by_contra! hn
  have hn' : A.eval 0 ≤ 0 := by
    rw [←coeff_zero_eq_eval_zero,show A=a.map (Int.castRingHom ℝ) from rfl,coeff_map]
    change ((a.coeff 0:ℤ):ℝ) ≤ 0
    exact_mod_cast hn
  obtain ⟨y,hy,hroot⟩ := intermediate_value_Icc hz A.continuous.continuousOn ⟨hn',hz'⟩
  have hr : A.IsRoot y := hroot
  exact (real_jones_positive m j hm y hy.1).ne' (hr.dvd (Polynomial.map_dvd _ hdiv))

private lemma factor_even_of_odd_N {m j : ℕ} (hm : 2 ≤ m) {a : ℤ[X]} (ha : a.Monic)
    (hdiv : a ∣ jonesSumPolynomial m j) (hn : Odd (j+1)) : Even a.natDegree := by
  by_contra! h
  have hodd : Odd (a.map (Int.castRingHom ℝ)).natDegree := by
    simpa [ha.natDegree_map] using (Nat.not_even_iff_odd.mp h)
  let A := a.map (Int.castRingHom ℝ)
  have hmA : A.Monic := ha.map _
  have hodd' : Odd A.natDegree := hodd
  have hpA : 0 < A.natDegree := by obtain ⟨v,hv⟩ := hodd'; omega
  have top := A.tendsto_atTop_of_leadingCoeff_nonneg (natDegree_pos_iff_degree_pos.mp hpA)
    (by rw [hmA.leadingCoeff]; norm_num)
  have bot := (A.comp (-X)).tendsto_atBot_of_leadingCoeff_nonpos
    (natDegree_pos_iff_degree_pos.mp (by simpa [natDegree_comp] using hpA))
    (by rw [comp_neg_X_leadingCoeff_eq,hmA.leadingCoeff,hodd'.neg_one_pow]; norm_num)
  obtain ⟨x,hx⟩ := (bot.eventually (Filter.eventually_le_atBot 0)).exists
  obtain ⟨y,hy⟩ := (top.eventually_ge_atTop 0).exists
  obtain ⟨z,hz⟩ := intermediate_value_univ (-x) y A.continuous (show 0 ∈ Set.Icc (A.eval (-x)) (A.eval y) from ⟨by simpa using hx,hy⟩)
  have hroot : (a.map (Int.castRingHom ℝ)).IsRoot z := hz
  have hp := hroot.dvd (Polynomial.map_dvd _ hdiv)
  by_cases hz : 0 ≤ z
  · exact (real_jones_positive m j (by omega) z hz).ne' hp
  have hz' : z < 0 := lt_of_not_ge hz
  have id := congrArg (fun f : ℝ[X] => f.eval z) (geom_map (Int.castRingHom ℝ) m j)
  change ((jonesSumPolynomial m j).map _).eval z=0 at hp
  simp only [eval_mul,eval_sub,eval_one,eval_add,eval_C,eval_pow,eval_X,Int.coe_castRingHom,
    Int.cast_natCast,hp,mul_zero] at id
  have hneg := hn.pow_neg hz'
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hcoef : 0 < (m:ℝ)-1 := by linarith
  linarith [mul_neg_of_pos_of_neg hcoef hz']

/-- The constant of every nonconstant monic factor is positive and its (j+1)-st
power is one modulo m−1. -/
theorem jones_factor_constant_congruence {m j : ℕ} (hm : 3 ≤ m) (hj : 0 < j)
    {a : ℤ[X]} (ha : a.Monic) (hd : 0 < a.natDegree) (hdiv : a ∣ jonesSumPolynomial m j) :
    0 < a.coeff 0 ∧ (a.coeff 0 : ZMod (m-1))^(j+1) = 1 := by
  have h := factor_signed_constant hm hj ha hdiv
  have he : Even (a.natDegree*(j+1)) := by
    by_cases hn : Even (j+1)
    · exact hn.mul_left _
    · exact (factor_even_of_odd_N (by omega) ha hdiv (Nat.not_even_iff_odd.mp hn)).mul_right _
  rw [he.neg_one_pow,one_mul] at h
  exact ⟨monic_factor_positive (by omega) ha hd hdiv,h⟩

private lemma constant_split {m j : ℕ} (hm : 3 ≤ m) (hj : 0 < j)
    (hred : ¬Irreducible ((jonesSumPolynomial m j).map (Int.castRingHom ℚ))) :
    ∃ u v : ℕ, 1<u ∧ 1<v ∧ u*v=m ∧
      (u:ZMod (m-1))^(j+1)=1 ∧ (v:ZMod (m-1))^(j+1)=1 := by
  by_contra hex
  apply hred
  obtain ⟨hd,hmon⟩ := jonesSumPolynomial_shape m j
  have mon := hmon hj
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast mon.isPrimitive).mp
  apply mon.irreducible_iff_natDegree.mpr
  refine ⟨fun h => by rw [h,natDegree_one] at hd; omega,?_⟩
  intro a b ha hb hab
  by_contra! hn
  have get (f : ℤ[X]) (hf : f.Monic) (hdeg : f.natDegree ≠ 0) (hdiv : f ∣ jonesSumPolynomial m j) :
      1 < (f.coeff 0).natAbs ∧ ((f.coeff 0).natAbs:ZMod (m-1))^(j+1)=1 := by
    obtain ⟨hpos,hpow⟩ := jones_factor_constant_congruence hm hj hf (Nat.pos_of_ne_zero hdeg) hdiv
    refine ⟨jones_factor_constant_gt_one (by omega) hf hdiv (Nat.pos_of_ne_zero hdeg),?_⟩
    have he : ((f.coeff 0).natAbs:ℤ) = f.coeff 0 := by rw [Int.natCast_natAbs,abs_of_pos hpos]
    have hc := congrArg (Int.castRingHom (ZMod (m-1))) he
    have hc' : ((f.coeff 0).natAbs:ZMod (m-1)) = (f.coeff 0:ZMod (m-1)) := by
      simpa only [Int.coe_castRingHom,Int.cast_natCast] using hc
    rwa [hc']
  obtain ⟨h₁,v₁⟩ := get a ha hn.1 (hab ▸ dvd_mul_right ..)
  obtain ⟨h₂,v₂⟩ := get b hb hn.2 (hab ▸ dvd_mul_left ..)
  have hab0 : a.coeff 0*b.coeff 0=m := by
    have h := congrArg (fun p : ℤ[X] => p.coeff 0) hab
    simpa [jonesSumPolynomial,finsetSum_coeff,coeff_X_pow] using h
  apply hex
  exact ⟨_,_,h₁,h₂,by simpa [Int.natAbs_mul] using congrArg Int.natAbs hab0,v₁,v₂⟩

/-- Reducibility forces some proper divisor c of the constant term, with c² ≤ m,
to have multiplicative order dividing j+1 modulo m−1. -/
theorem jones_reducible_implies_small_divisor {m j : ℕ} (hm : 3 ≤ m) (hj : 0 < j)
    (hred : ¬Irreducible ((jonesSumPolynomial m j).map (Int.castRingHom ℚ))) :
    ∃ c : ℕ, 1<c ∧ c*c ≤ m ∧ c ∣ m ∧ (c:ZMod (m-1))^(j+1)=1 := by
  obtain ⟨u,v,hu,hv,hprod,hou,hov⟩ := constant_split hm hj hred
  rcases le_total u v with h|h
  · exact ⟨u,hu,hprod ▸ Nat.mul_le_mul_left u h,hprod ▸ dvd_mul_right ..,hou⟩
  · exact ⟨v,hv,hprod ▸ Nat.mul_le_mul_right v h,hprod ▸ dvd_mul_left ..,hov⟩

-- A proper divisor of T is at most T/2. A smaller order would force (M+1)^2 ≤ 3M+1.
private lemma two_order_exact (M T : ℕ) (hM : 1 < M) (he : 3*M+1=2^T) :
    orderOf (2:ZMod M) = T := by
  have powmod : (2:ZMod M)^T=1 := by
    have h := congrArg (fun n : ℕ => (n:ZMod M)) he
    simpa using h.symm
  let e := orderOf (2:ZMod M)
  have ht : 0 < T := by
    by_contra! h
    have hz : T=0 := by omega
    simp [hz] at he
    omega
  have hpos : 0 < e := orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨T,ht,powmod⟩)
  obtain ⟨k,hk⟩ := orderOf_dvd_of_pow_eq_one powmod
  by_contra hne
  have hk' : 2 ≤ k := by
    by_contra! hh
    interval_cases k <;> simp_all [e]
  have hdouble : e+e ≤ T := by
    change T=e*k at hk
    simpa [hk,Nat.mul_two] using (Nat.mul_le_mul_left e hk')
  have hnat : 2^e ≡ 1 [MOD M] := by
    apply (ZMod.natCast_eq_natCast_iff ..).mp
    simp [e,pow_orderOf_eq_one]
  have h₂ : 1 < 2^e := Nat.one_lt_pow hpos.ne' (by decide)
  have hdiv := (Nat.modEq_iff_dvd' h₂.le).mp hnat.symm
  have H := Nat.le_of_dvd (by omega : 0 < 2^e-1) hdiv
  have hup := Nat.pow_le_pow_right (by decide : 0 < 2) hdouble
  rw [pow_add,←he] at hup
  nlinarith [Nat.mul_le_mul (by omega : M+1 ≤ 2^e) (by omega : M+1 ≤ 2^e)]

/-- At every Jones parameter with prime odd part, reducibility is confined to
the single degree class j ≡ t modulo t+1. -/
theorem jones_semiprime_degree_obstruction (t j : ℕ) (ho : Odd t)
    (hp : ((2^t+1)/3).Prime) (hj : 0 < j)
    (hred : ¬Irreducible ((jonesSumPolynomial (jonesConstant t) j).map (Int.castRingHom ℚ))) :
    t+1 ∣ j+1 := by
  let q := (2^t+1)/3
  let m := jonesConstant t
  have hq : q.Prime := hp
  have hm : m=2*q := rfl
  have hm' : 3 ≤ m := by have := hq.two_le; omega
  obtain ⟨u,v,hu,hv,huv,ou,ov⟩ := constant_split hm' hj hred
  have hqdiv : q ∣ u*v := by rw [huv,hm]; exact dvd_mul_left ..
  have htwo : (2:ZMod (m-1))^(j+1)=1 := by
    rcases hq.dvd_mul.mp hqdiv with h|h
    · have hle := Nat.le_of_dvd (by omega : 0<u) h
      have h : v=2 := by nlinarith [Nat.mul_le_mul_right v hle,hq.two_le]
      simpa [h] using ov
    · have hle := Nat.le_of_dvd (by omega : 0<v) h
      have h : u=2 := by nlinarith [Nat.mul_le_mul_left u hle,hq.two_le]
      simpa [h] using ou
  have h3 : 3 ∣ 2^t+1 := by simpa using ho.nat_add_dvd_pow_add_pow 2 1
  have hd : q*3=2^t+1 := Nat.div_mul_cancel h3
  have he : 3*(m-1)+1=2^(t+1) := by rw [pow_succ]; omega
  rw [←two_order_exact (m-1) (t+1) (by omega) he]
  exact orderOf_dvd_of_pow_eq_one htwo

/-- At the first Jones parameter with composite odd part (t=9, m=342),
only j+1 divisible by 10 or by 15 can be reducible. -/
theorem jones_nine_degree_obstruction {j : ℕ} (hj : 0 < j)
    (hred : ¬Irreducible ((jonesSumPolynomial (jonesConstant 9) j).map (Int.castRingHom ℚ))) :
    10 ∣ j+1 ∨ 15 ∣ j+1 := by
  obtain ⟨c,hc,hs,hd,hpow⟩ := jones_reducible_implies_small_divisor (m:=342) (by decide) hj hred
  have hc' : c<19 := by nlinarith
  have table : ∀ a : Fin 19, 1<a.val → a.val ∣ 342 →
      (a.val:ZMod 341)^30=1 ∧ ∀ i : Fin 30, (a.val:ZMod 341)^i.val=1 → 10 ∣ i.val ∨ 15 ∣ i.val := by decide
  obtain ⟨period,test⟩ := table ⟨c,hc'⟩ hc hd
  have hr : (c:ZMod 341)^((j+1)%30) = 1 := by
    have step := congrArg (fun n => (c:ZMod 341)^n) (Nat.mod_add_div (j+1) 30)
    simp only [pow_add,pow_mul,period,one_pow,mul_one] at step
    exact step.trans (by simpa only [pow_add,pow_one] using hpow)
  have h := test ⟨_,Nat.mod_lt (j+1) (by decide : 0<30)⟩ hr
  change 10 ∣ (j+1)%30 ∨ 15 ∣ (j+1)%30 at h
  omega

#print axioms jones_factor_constant_congruence
#print axioms jones_reducible_implies_small_divisor
#print axioms jones_semiprime_degree_obstruction
#print axioms jones_nine_degree_obstruction

end CunninghamChain
