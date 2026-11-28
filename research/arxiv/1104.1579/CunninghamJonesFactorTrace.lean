import Mathlib
import research.arxiv.«1104.1579».CunninghamJonesFactorOrders

/-! Bounds for the degrees of Jones polynomial factors with constant term two. -/

namespace CunninghamChain
open Polynomial
open scoped Polynomial

private lemma first_order_power (M b : ℤ) (k : ℕ) :
    (1+M*b)^k ≡ 1+M*(b*k) [ZMOD M^2] := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ (1+M*b)]
    refine (ih.mul_right _).trans ?_
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-(b^2*k),?_⟩
    push_cast
    ring

private lemma scale_value_first_order (A : ℤ[X]) (ha : A.Monic) (hd : 0 < A.natDegree) (M : ℤ) :
    (A.scaleRoots M).eval (1+M) ≡ 1+M*(A.natDegree+A.nextCoeff) [ZMOD M^2] := by
  obtain ⟨n,he⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  have low : M^2 ∣ ∑ i ∈ Finset.range n, (A.scaleRoots M).coeff i*(1+M)^i := by
    apply Finset.dvd_sum
    intro i hi
    rw [coeff_scaleRoots]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (pow_dvd_pow M (by have := Finset.mem_range.mp hi; omega)) _) _
  have top : A.coeff (n+1) = 1 := by simpa only [he] using ha.coeff_natDegree
  have nx : A.coeff n=A.nextCoeff := by
    rw [nextCoeff_of_natDegree_pos hd,he,Nat.succ_sub_one]
  rw [eval_eq_sum_range,natDegree_scaleRoots,he,Finset.sum_range_succ,Finset.sum_range_succ]
  simp only [coeff_scaleRoots,he,top,nx,show n.succ-n=1 by omega,Nat.sub_self,pow_zero,mul_one,one_mul,pow_one] at low ⊢
  have hz := Int.modEq_zero_iff_dvd.mpr low
  have h1 := first_order_power M 1 n
  have h2 := first_order_power M 1 (n+1)
  simp only [mul_one,one_mul] at h1 h2
  refine ((hz.add (h1.mul_left (A.nextCoeff*M))).add h2).trans ?_
  apply Int.modEq_iff_dvd.mpr
  refine ⟨-(A.nextCoeff*n),?_⟩
  push_cast
  ring

private lemma scaled_root_product (A : ℂ[X]) (ha : A.Monic) (m M : ℂ) (hM : M ≠ 0)
    (N : ℕ) (hN : Even N) (hz : ∀ z ∈ A.roots, z^N = m-M*z) :
    (A.scaleRoots M).eval m = (A.coeff 0)^N := by
  rw [(IsAlgClosed.splits _).eval_eq_prod_roots_of_monic ((monic_scaleRoots_iff M).mpr ha),
    roots_scaleRoots _ (isUnit_iff_ne_zero.mpr hM),Multiset.map_map]
  have hprod : (A.roots.map ((m - ·) ∘ (M * ·))).prod = (A.roots.map (fun z => z^N)).prod := by
    congr 1
    exact Multiset.map_congr rfl (fun z h => (hz z h).symm)
  rw [hprod,(IsAlgClosed.splits A).coeff_zero_eq_prod_roots_of_monic ha,mul_pow,
    ←pow_mul,(hN.mul_left _).neg_one_pow,one_mul]
  simpa using (Multiset.prod_map_pow (m := A.roots) (f := id) (n := N))

private lemma geom_value (m j : ℕ) (z : ℂ) :
    (z-1)*((jonesSumPolynomial m j).map (Int.castRingHom ℂ)).eval z =
      z^(j+1)+((m:ℂ)-1)*z-m := by
  induction j with
  | zero => simp [jonesSumPolynomial]; ring
  | succ j ih =>
    rw [jonesSumPolynomial_succ,Polynomial.map_add,Polynomial.map_pow,Polynomial.map_X,
      eval_add,eval_pow,eval_X,mul_add,ih,pow_succ z (j+1)]
    ring

/-- At odd Jones degrees the value of a scaled monic factor at the original constant
equals the corresponding power of its own constant. -/
theorem jones_scaled_factor_value {m j : ℕ} (hm : 2 ≤ m) (hN : Even (j+1))
    {A : ℤ[X]} (ha : A.Monic) (hdiv : A ∣ jonesSumPolynomial m j) :
    (A.scaleRoots ((m:ℤ)-1)).eval (m:ℤ) = (A.coeff 0)^(j+1) := by
  let f := Int.castRingHom ℂ
  have hm0 : f ((m:ℤ)-1) ≠ 0 := by
    change (((m:ℤ)-1:ℤ):ℂ) ≠ 0
    exact_mod_cast (show (m:ℤ)-1 ≠ 0 by omega)
  have h := scaled_root_product (A.map f) (ha.map f) (f m) (f ((m:ℤ)-1)) hm0 (j+1) hN (by
    intro z hz
    have hroot := (isRoot_of_mem_roots hz).dvd (Polynomial.map_dvd f hdiv)
    have e := geom_value m j z
    change ((jonesSumPolynomial m j).map f).eval z=0 at hroot
    change (z-1)*((jonesSumPolynomial m j).map f).eval z=_ at e
    rw [hroot,mul_zero] at e
    simp only [f,Int.coe_castRingHom,Int.cast_sub,Int.cast_one,Int.cast_natCast]
    linear_combination -e)
  apply (Int.cast_injective (α := ℂ))
  rw [←map_scaleRoots _ _ f (by simp [ha.leadingCoeff]),eval_map_apply,coeff_map,←map_pow] at h
  exact h

/-- For a constant-two factor in the surviving class j+1 = k(t+1), one higher
power of m−1 in the norm identity detects the next coefficient. -/
theorem jones_factor_trace_congruence {t j k : ℕ} (ho : Odd t) (hm : 2 ≤ jonesConstant t)
    (hlen : j+1=(t+1)*k) {A : ℤ[X]} (ha : A.Monic) (hd : 0<A.natDegree)
    (hdiv : A ∣ jonesSumPolynomial (jonesConstant t) j) (hc : A.coeff 0=2) :
    (A.natDegree:ℤ)+A.nextCoeff ≡ 3*k [ZMOD (jonesConstant t:ℤ)-1] := by
  let M := (jonesConstant t:ℤ)-1
  have hM : M ≠ 0 := by dsimp [M]; omega
  have h3 : 3 ∣ 2^t+1 := by simpa using ho.nat_add_dvd_pow_add_pow 2 1
  have hnat : 3*jonesConstant t=2*(2^t+1) := by
    have := Nat.div_mul_cancel h3
    unfold jonesConstant
    omega
  have ht : (2:ℤ)^(t+1)=1+M*3 := by
    have hz : (3:ℤ)*jonesConstant t=2*(2^t+1) := by exact_mod_cast hnat
    dsimp [M]
    rw [pow_succ]
    linarith
  have heven : Even (j+1) := by rw [hlen]; exact (ho.add_one).mul_right _
  have hnorm := jones_scaled_factor_value hm heven ha hdiv
  rw [hc,hlen,pow_mul,ht] at hnorm
  have h := scale_value_first_order A ha hd M
  rw [show 1+M=(jonesConstant t:ℤ) by dsimp [M]; ring,hnorm] at h
  have h' := Int.modEq_iff_dvd.mp (h.symm.trans (first_order_power M 3 k))
  apply Int.modEq_iff_dvd.mpr
  obtain ⟨v,hv⟩ := h'
  exact ⟨v,mul_left_cancel₀ hM (by linear_combination hv)⟩

private lemma root_size_estimate {m j : ℕ} (hm : j < m) {z : ℂ}
    (hz : ((jonesSumPolynomial m j).map (Int.castRingHom ℂ)).IsRoot z) :
    1 < ‖z‖ ∧ (m:ℝ) ≤ j * ‖z‖^j := by
  have hs : (m:ℂ) + ∑ i ∈ Finset.range j, z^(i+1) = 0 := by
    simpa [Polynomial.IsRoot,jonesSumPolynomial,Polynomial.map_sum,eval_finsetSum] using hz
  have hn := congrArg norm (eq_neg_of_add_eq_zero_left hs)
  rw [Complex.norm_natCast,norm_neg] at hn
  have est (R : ℝ) (hR : 1 ≤ R) (hr : ‖z‖ ≤ R) : (m:ℝ) ≤ j*R^j := by
    rw [hn]
    refine (norm_sum_le ..).trans ?_
    calc ∑ i ∈ Finset.range j, ‖z^(i+1)‖ ≤ ∑ _i ∈ Finset.range j, R^j := by
           apply Finset.sum_le_sum
           intro i hi
           rw [norm_pow]
           exact (pow_le_pow_left₀ (norm_nonneg _) hr _).trans
             (pow_le_pow_right₀ hR (Finset.mem_range.mp hi))
         _ = _ := by simp
  have hsep : 1 < ‖z‖ := by
    by_contra! h
    have he := est 1 le_rfl h
    simp at he
    omega
  exact ⟨hsep,est _ hsep.le le_rfl⟩

private lemma root_product_estimate (m j : ℕ) (s : Multiset ℂ)
    (h : ∀ z ∈ s, (m:ℝ) ≤ j*‖z‖^j) :
    (m:ℝ)^s.card ≤ (j:ℝ)^s.card * ‖s.prod‖^j := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    have hz := h z (Multiset.mem_cons_self ..)
    have hs := ih (fun a ha => h a (Multiset.mem_cons_of_mem ha))
    simpa only [Multiset.card_cons,Multiset.prod_cons,norm_mul,pow_succ,mul_pow,
      mul_assoc,mul_left_comm,mul_comm] using mul_le_mul hs hz (by positivity) (by positivity)

private lemma root_sum_estimate (s : Multiset ℂ) (h : ∀ z ∈ s, 1 < ‖z‖) :
    1 ≤ ‖s.prod‖ ∧ (s ≠ 0 → 1 < ‖s.prod‖) ∧
    (s.map norm).sum ≤ (s.card:ℝ)+‖s.prod‖-1 ∧
    (1 < s.card → (s.map norm).sum < (s.card:ℝ)+‖s.prod‖-1) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    obtain ⟨h1,h2,h3,_⟩ := ih (fun a ha => h a (Multiset.mem_cons_of_mem ha))
    have hz := h z (Multiset.mem_cons_self ..)
    simp only [Multiset.prod_cons,norm_mul,Multiset.map_cons,Multiset.sum_cons,Multiset.card_cons,Nat.cast_add_one]
    have hp := one_lt_mul_of_lt_of_le hz h1
    refine ⟨hp.le,fun _ => hp,?_,?_⟩
    · nlinarith [mul_nonneg (sub_nonneg.mpr hz.le) (sub_nonneg.mpr h1)]
    · intro hc
      have hne : s ≠ 0 := by rintro rfl; simp at hc
      nlinarith [mul_pos (sub_pos.mpr hz) (sub_pos.mpr (h2 hne))]

private lemma factor_estimates {m j : ℕ} (hm : j < m) {A : ℤ[X]} (ha : A.Monic)
    (hdiv : A ∣ jonesSumPolynomial m j) (hc : A.coeff 0 = 2) :
    m^A.natDegree ≤ j^A.natDegree*2^j ∧
    (1 < A.natDegree → |A.nextCoeff| ≤ (A.natDegree:ℤ)) := by
  let f := Int.castRingHom ℂ
  let G := A.map f
  have hg : G.Monic := ha.map f
  have hdegree : G.natDegree = A.natDegree := ha.natDegree_map _
  have hcard : G.roots.card=A.natDegree := (IsAlgClosed.splits G).natDegree_eq_card_roots.symm.trans hdegree
  have hr (z : ℂ) (hz : z ∈ G.roots) :=
    root_size_estimate hm ((isRoot_of_mem_roots hz).dvd (Polynomial.map_dvd f hdiv))
  have hprod := congrArg norm ((IsAlgClosed.splits G).coeff_zero_eq_prod_roots_of_monic hg)
  have he : ‖G.roots.prod‖ = 2 := by
    change ‖(A.map f).coeff 0‖ = _ at hprod
    simpa [coeff_map,hc,f,norm_mul] using hprod.symm
  have est := root_product_estimate m j G.roots fun z hz => (hr z hz).2
  rw [hcard,he] at est
  refine ⟨by exact_mod_cast est,?_⟩
  intro hd
  have hsum := (root_sum_estimate G.roots fun z hz => (hr z hz).1).2.2.2 (hcard ▸ hd)
  rw [hcard,he] at hsum
  have hnorm := congrArg norm ((IsAlgClosed.splits G).nextCoeff_eq_neg_sum_roots_of_monic hg)
  have hnext : G.nextCoeff=f A.nextCoeff :=
    nextCoeff_map_of_leadingCoeff_ne_zero f (by simp [ha.leadingCoeff])
  rw [hnext,norm_neg] at hnorm
  change ‖(A.nextCoeff:ℂ)‖ = _ at hnorm
  rw [Complex.norm_intCast] at hnorm
  have hlt : (|A.nextCoeff|:ℤ) < (A.natDegree:ℤ)+1 := by
    exact_mod_cast (show (↑|A.nextCoeff|:ℝ) < (A.natDegree:ℝ)+1 by
      rw [Int.cast_abs,hnorm]
      linarith [norm_multiset_sum_le G.roots])
  omega

/-- The size and trace bounds for every constant-two factor apply even when
the odd part of the Jones constant is composite. -/
theorem jones_constant_two_degree_bounds {t j k : ℕ} (ho : Odd t) (hm : j < jonesConstant t)
    (hk : 2 ≤ k) (hsep : 3*k < jonesConstant t-1) (hlen : j+1 = (t+1)*k)
    {A : ℤ[X]} (ha : A.Monic) (hd : 0 < A.natDegree)
    (hdiv : A ∣ jonesSumPolynomial (jonesConstant t) j) (hc : A.coeff 0=2) :
    3*k ≤ 2*A.natDegree ∧ (jonesConstant t)^A.natDegree ≤ j^A.natDegree*2^j := by
  have ht := jones_factor_trace_congruence ho (by omega) hlen ha hd hdiv hc
  obtain ⟨hsize,hn⟩ := factor_estimates hm ha hdiv hc
  refine ⟨?_,hsize⟩
  by_contra! hlt
  have H : 0 ≤ (A.natDegree:ℤ)+A.nextCoeff ∧ (A.natDegree:ℤ)+A.nextCoeff < 3*k := by
    by_cases h1 : A.natDegree=1
    · have he : A.nextCoeff=2 := by rw [nextCoeff_of_natDegree_pos hd,h1]; exact hc
      omega
    · obtain ⟨hlo,hup⟩ := abs_le.mp (hn (by omega))
      omega
  have hlarge := Int.le_of_dvd (by omega : 0 < 3*(k:ℤ)-((A.natDegree:ℤ)+A.nextCoeff))
    (Int.modEq_iff_dvd.mp ht)
  omega

private lemma size_excludes (m t j k e : ℕ) (hj : 0<j) (hlen : j+1=(t+1)*k)
    (hdeg : 3*k ≤ 2*e) (hsize : m^e ≤ j^e*2^j)
    (hcut : j^3*2^(2*(t+1)) ≤ m^3) : False := by
  have H : j^(3*e)*2^((2*(t+1))*e) ≤ j^(3*e)*2^(j*3) := by
    calc j^(3*e)*2^((2*(t+1))*e) = (j^3*2^(2*(t+1)))^e := by rw [mul_pow,pow_mul,pow_mul]
         _ ≤ (m^3)^e := Nat.pow_le_pow_left hcut _
         _ = (m^e)^3 := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
         _ ≤ (j^e*2^j)^3 := Nat.pow_le_pow_left hsize _
         _ = _ := by rw [mul_pow,←pow_mul,←pow_mul,Nat.mul_comm e 3]
  have he := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (Nat.le_of_mul_le_mul_left H (Nat.pow_pos hj))
  nlinarith only [he,hlen,Nat.mul_le_mul_left (t+1) hdeg]

private lemma constant_two_factor {q j : ℕ} (hq : q.Prime) (hj : 0<j)
    (hred : ¬Irreducible ((jonesSumPolynomial (2*q) j).map (Int.castRingHom ℚ))) :
    ∃ A : ℤ[X], A.Monic ∧ 0<A.natDegree ∧ A ∣ jonesSumPolynomial (2*q) j ∧ A.coeff 0=2 := by
  by_contra! hnone
  apply hred
  obtain ⟨hdeg,hmon⟩ := jonesSumPolynomial_shape (2*q) j
  have mon := hmon hj
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast mon.isPrimitive).mp
  apply mon.irreducible_iff_natDegree.mpr
  refine ⟨fun h => by rw [h,natDegree_one] at hdeg; omega,?_⟩
  intro a b ha hb hab
  by_contra! hn
  have hda := hab ▸ dvd_mul_right a b
  have hdb := hab ▸ dvd_mul_left b a
  have props (A : ℤ[X]) (hA : A.Monic) (hd : A.natDegree ≠ 0) (hdiv : A ∣ jonesSumPolynomial (2*q) j) :
      2 < (A.coeff 0).natAbs := by
    have hp := (jones_factor_constant_congruence (by have := hq.two_le; omega) hj hA (Nat.pos_of_ne_zero hd) hdiv).1
    have hgt := jones_factor_constant_gt_one (by have := hq.two_le; omega) hA hdiv (Nat.pos_of_ne_zero hd)
    have hneq := hnone A hA (Nat.pos_of_ne_zero hd) hdiv
    omega
  have hu := props a ha hn.1 hda
  have hv := props b hb hn.2 hdb
  have hconst : (a.coeff 0).natAbs*(b.coeff 0).natAbs=2*q := by
    rw [←Int.natAbs_mul,←mul_coeff_zero,hab]
    simp [jonesSumPolynomial,finsetSum_coeff,coeff_X_pow,Int.natAbs_mul]
  have hqd : q ∣ (a.coeff 0).natAbs*(b.coeff 0).natAbs := hconst ▸ dvd_mul_left ..
  rcases hq.dvd_mul.mp hqd with h|h
  · have he := Nat.le_of_dvd (by omega : 0<(a.coeff 0).natAbs) h
    nlinarith [Nat.mul_le_mul_right (b.coeff 0).natAbs he,hq.two_le]
  · have he := Nat.le_of_dvd (by omega : 0<(b.coeff 0).natAbs) h
    nlinarith [Nat.mul_le_mul_left (a.coeff 0).natAbs he,hq.two_le]

/-- At Jones parameters with prime odd part, the predicted classification holds
through the range j³·2^(2(t+1)) ≤ m³. -/
theorem jones_exponential_degree_range (t j : ℕ) (ht : 3 ≤ t) (ho : Odd t)
    (hp : ((2^t+1)/3).Prime) (hj : 0 < j)
    (hcut : j^3*2^(2*(t+1)) ≤ (jonesConstant t)^3) :
    Irreducible ((jonesSumPolynomial (jonesConstant t) j).map (Int.castRingHom ℚ)) ↔ j ≠ t := by
  constructor
  · intro hi heq
    subst j
    have hr := (jones_rational_root_iff t t ht ho (by omega) (by nlinarith) (-2)).mpr ⟨rfl,rfl⟩
    have hd := natDegree_eq_of_degree_eq_some (degree_eq_one_of_irreducible_of_root hi hr)
    rw [natDegree_map_eq_of_injective Int.cast_injective,(jonesSumPolynomial_shape _ _).1] at hd
    change t = 1 at hd
    omega
  · intro hne
    by_contra hred
    obtain ⟨k,hlen⟩ := jones_semiprime_degree_obstruction t j ho hp hj hred
    have hk : 2 ≤ k := by
      rcases k with _|(_|k) <;> simp_all
    have h4 : 4*j ≤ jonesConstant t := by
      apply (Nat.pow_le_pow_iff_left (by decide : (3:ℕ) ≠ 0)).mp
      rw [mul_pow,Nat.mul_comm (4^3)]
      exact (Nat.mul_le_mul_left _ (show 2^6 ≤ 2^(2*(t+1)) from
        Nat.pow_le_pow_right (by decide) (by omega))).trans hcut
    obtain ⟨A,ha,hd,hdiv,hc⟩ := constant_two_factor hp hj hred
    have hk4 : 4*k ≤ j+1 := hlen ▸ Nat.mul_le_mul_right k (by omega : 4 ≤ t+1)
    obtain ⟨hdegree,hsize⟩ := jones_constant_two_degree_bounds ho (by omega) hk (by omega) hlen ha hd hdiv hc
    exact size_excludes _ t j k A.natDegree hj hlen hdegree hsize hcut

private lemma wagstaff_43_prime : Nat.Prime 2932031007403 := by
  apply lucas_primality _ 3 (by reduce_mod_char)
  intro q hq hdiv
  change q ∣ 2*3*7*7*43*127*337*5419 at hdiv
  simp only [hq.dvd_mul,Nat.prime_dvd_prime_iff_eq hq (by norm_num1 : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num1 : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num1 : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num1 : Nat.Prime 43),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num1 : Nat.Prime 127),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num1 : Nat.Prime 337),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num1 : Nat.Prime 5419)] at hdiv
  rcases hdiv with (((((((rfl|rfl)|rfl)|rfl)|rfl)|rfl)|rfl)|rfl) <;> reduce_mod_char <;> decide

/-- At t=43 the complete prefix through degree 8669 contains only the
prescribed reducible polynomial in degree 43. -/
theorem jones_forty_three_degree_range (j : ℕ) (hj : 0 < j) (hmax : j ≤ 8669) :
    Irreducible ((jonesSumPolynomial (jonesConstant 43) j).map (Int.castRingHom ℚ)) ↔ j ≠ 43 := by
  apply jones_exponential_degree_range 43 j (by decide) (by decide) wagstaff_43_prime hj
  exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hmax 3)).trans (by decide)

#print axioms jones_scaled_factor_value
#print axioms jones_factor_trace_congruence
#print axioms jones_constant_two_degree_bounds
#print axioms jones_exponential_degree_range
#print axioms jones_forty_three_degree_range

end CunninghamChain
