import Mathlib
import FormalConjectures.Arxiv.«1104.1579».CunninghamChain

/-!
# Linear factors in Jones's polynomial reducibility conjecture

At odd parameter `t`, Jones takes the constant term `2(2^t+1)/3`.
A negative integer root other than −2 is forced into a narrow degree range.
-/

namespace CunninghamChain
open Polynomial

/-- Jones's positive-coefficient polynomial with constant term `m` and degree `j`. -/
noncomputable def jonesSumPolynomial (m j : ℕ) : ℤ[X] :=
  C (m : ℤ) + ∑ i ∈ Finset.range j, X^(i+1)

/-- A second even root magnitude must be large modulo a power of two.
Combined with the geometric sum, this confines its degree. -/
private lemma alternative_root_degree (m t j b : ℕ) (hj : 0 < j)
    (hb : 2 < b) (heven : 2 ∣ b) (hm : 3*m = 2*(2^t+1)) (hmt : m < 2^t)
    (hbm : b ≤ m) (hroot : b^(j+1)+b = m*(b+1)) : j*(j+1) < t := by
  let e := min j t + 1
  have hjd : 2^e ∣ 3*b^(j+1) := dvd_mul_of_dvd_right
    (pow_dvd_pow_of_dvd_of_le heven (by dsimp [e]; omega : e ≤ j+1)) _
  have htd : 2^e ∣ 2^(t+1)*(b+1) :=
    dvd_mul_of_dvd_left (pow_dvd_pow 2 (by dsimp [e]; omega : e ≤ t+1)) _
  have he : 3*b^(j+1)+(b-2) = 2^(t+1)*(b+1) := by
    rw [pow_succ 2 t]
    have hsub : b-2+2=b := by omega
    nlinarith only [hsub,hroot,hm,congrArg (fun x : ℕ => x*b) hm]
  rw [←he] at htd
  have hsize := Nat.le_of_dvd (by omega : 0 < b-2) ((Nat.dvd_add_right hjd).mp htd)
  have hlt : j < t := by
    by_contra! hge
    dsimp [e] at hsize
    rw [min_eq_right hge,pow_succ] at hsize
    omega
  dsimp [e] at hsize
  rw [min_eq_left hlt.le] at hsize
  have hprod : (b+1)*(b-1)^j ≤ b^(j+1) := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    have hsq : (b+1)*(b-1) ≤ b^2 := by
      have := Nat.sub_add_cancel (by omega : 1 ≤ b)
      nlinarith
    have hpow := Nat.pow_le_pow_left (Nat.sub_le b 1) k
    calc
      (b+1)*(b-1)^(k+1) = ((b+1)*(b-1))*(b-1)^k := by ring
      _ ≤ b^2*b^k := Nat.mul_le_mul hsq hpow
      _ = b^(k+1+1) := by ring
  have hlow : (b-1)^j ≤ m := by
    exact Nat.le_of_mul_le_mul_left (show (b+1)*(b-1)^j ≤ (b+1)*m by
      nlinarith only [hprod,hroot]) (by omega)
  have hpow := Nat.pow_le_pow_left (by omega : 2^(j+1) ≤ b-1) j
  rw [←pow_mul,Nat.mul_comm (j+1) j] at hpow
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp ((hpow.trans hlow).trans_lt hmt)

/-- The even constant in Jones's Conjecture 4.1. -/
def jonesConstant (t : ℕ) : ℕ := 2*((2^t+1)/3)

private lemma constant_eq (t : ℕ) (ht : Odd t) : 3*jonesConstant t = 2*(2^t+1) := by
  have h : 3 ∣ 2^t+1 := by
    simpa using ht.nat_add_dvd_pow_add_pow 2 1
  have he := Nat.div_mul_cancel h
  unfold jonesConstant
  omega

/-- Adding the highest monomial extends the Jones sum by one degree. -/
lemma jonesSumPolynomial_succ (m j : ℕ) :
    jonesSumPolynomial m (j+1) = X^(j+1) + jonesSumPolynomial m j := by
  simp [jonesSumPolynomial,Finset.sum_range_succ]; ring

/-- The Jones sum has degree j and is monic in positive degrees. -/
lemma jonesSumPolynomial_shape (m j : ℕ) : (jonesSumPolynomial m j).natDegree = j ∧
    (0 < j → (jonesSumPolynomial m j).Monic) := by
  induction j with
  | zero => simp [jonesSumPolynomial]
  | succ j ih =>
    rw [jonesSumPolynomial_succ]
    have h : (jonesSumPolynomial m j).natDegree < (X^(j+1) : ℤ[X]).natDegree := by simp [ih.1]
    exact ⟨(natDegree_add_eq_left_of_natDegree_lt h).trans (by simp),
      fun _ => monic_X_pow_add (by simpa using degree_lt_degree h)⟩

private lemma sum_eval (m j : ℕ) (x : ℤ) :
    (jonesSumPolynomial m j).eval x = m + ∑ i ∈ Finset.range j, x^(i+1) := by
  induction j with
  | zero => simp [jonesSumPolynomial]
  | succ j ih => rw [jonesSumPolynomial_succ,eval_add,eval_pow,eval_X,ih,Finset.sum_range_succ]; ring

private lemma geometric_identity (m j : ℕ) (x : ℤ) :
    (x-1)*(jonesSumPolynomial m j).eval x = x^(j+1)+((m:ℤ)-1)*x-m := by
  induction j with
  | zero => simp [jonesSumPolynomial]; ring
  | succ j ih =>
    rw [jonesSumPolynomial_succ,eval_add,eval_pow,eval_X,pow_succ x (j+1)]
    linear_combination ih

private lemma root_mod_two (m j b : ℕ) (hm : Even m) (hj : Odd j)
    (hr : (jonesSumPolynomial m j).eval (-(b:ℤ)) = 0) : 2 ∣ b := by
  by_contra h
  obtain ⟨k,hk⟩ : Odd b := Nat.odd_iff.mpr (by omega)
  obtain ⟨u,hu⟩ := hm
  obtain ⟨v,hv⟩ := hj
  rw [sum_eval] at hr
  have hh := congrArg (Int.castRingHom (ZMod 2)) hr
  change (((m : ℤ) + ∑ i ∈ Finset.range j, (-(b:ℤ))^(i+1) : ℤ) : ZMod 2) = 0 at hh
  push_cast at hh
  have h2 : (2 : ZMod 2) = 0 := by decide
  have hb' : (b : ZMod 2) = 1 := by rw [hk]; push_cast; rw [h2]; ring
  have hm' : (m : ZMod 2) = 0 := by rw [hu,Nat.cast_add,←two_mul,h2,zero_mul]
  have hj' : (j : ZMod 2) = 1 := by rw [hv]; push_cast; rw [h2]; ring
  simp [hb',hm',show (-1:ZMod 2) = 1 by decide,hj'] at hh

private lemma root_magnitude (m t j : ℕ) (ht : 3 ≤ t) (hodd : Odd t)
    (hm : m = jonesConstant t) (hj : 0 < j) (x : ℚ)
    (hr : ((jonesSumPolynomial m j).map (Int.castRingHom ℚ)).IsRoot x) :
    (x = -2 ∧ j = t) ∨ j*(j+1) < t := by
  have h3 : 3*m = 2*(2^t+1) := hm ▸ constant_eq t hodd
  have ht8 : 8 ≤ 2^t := (Nat.pow_le_pow_right (by decide) ht : 2^3 ≤ 2^t)
  have hm₁ : 1 < m := by omega
  have hmt : m < 2^t := by omega
  have heval : aeval x (jonesSumPolynomial m j) = 0 := by
    rw [aeval_def,eval₂_eq_eval_map]; exact hr
  obtain ⟨z,hz,hdiv⟩ := exists_integer_of_is_root_of_monic ((jonesSumPolynomial_shape m j).2 hj) heval
  have he : (jonesSumPolynomial m j).eval z = 0 := by
    rw [hz,aeval_def,eval₂_at_apply] at heval
    change (((jonesSumPolynomial m j).eval z : ℤ) : ℚ) = 0 at heval
    exact_mod_cast heval
  have hneg : z < 0 := by
    by_contra! hz₀
    rw [sum_eval] at he
    have : 0 ≤ ∑ i ∈ Finset.range j, z^(i+1) := Finset.sum_nonneg fun _ _ => pow_nonneg hz₀ _
    omega
  let b := z.natAbs
  have hbz : z = -(b:ℤ) := by dsimp [b]; omega
  have hid := geometric_identity m j z
  rw [he,mul_zero,hbz] at hid
  have hjodd : Odd j := by
    by_contra ho
    have hev : Even j := Nat.not_odd_iff_even.mp ho
    rw [pow_succ,hev.neg_pow] at hid
    have hpos : 0 ≤ (b:ℤ)^j := by positivity
    nlinarith [show 0 ≤ ((m:ℤ)-1)*b by exact mul_nonneg (by omega) (Int.natCast_nonneg _)]
  have hb2 : 2 ∣ b := root_mod_two m j b (hm ▸ even_two_mul _) hjodd (hbz ▸ he)
  rw [pow_succ,hjodd.neg_pow] at hid
  have hroot : b^(j+1)+b = m*(b+1) := by
    zify; rw [pow_succ]; nlinarith only [hid]
  by_cases hb : b = 2
  · left
    constructor
    · rw [hz]; change (z:ℚ) = -2; exact_mod_cast (show z = -2 by omega)
    · rw [hb] at hroot
      have hp : 2^j = 2^t := by rw [pow_succ] at hroot; omega
      exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) hp
  · right
    have hb' : 2 < b := by omega
    have hbm : b ≤ m := by
      have hconst : (jonesSumPolynomial m j).coeff 0 = m := by
        simp [jonesSumPolynomial,finsetSum_coeff,coeff_X_pow]
      rw [hconst,hbz,neg_dvd] at hdiv
      exact Nat.le_of_dvd (by omega) (by exact_mod_cast hdiv)
    exact alternative_root_degree m t j b hj hb' hb2 h3 hmt hbm hroot

/-- Throughout this degree range, the sole rational root allowed by Jones's
family is −2 at the prescribed degree. -/
theorem jones_rational_root_iff (t j : ℕ) (ht : 3 ≤ t) (ho : Odd t)
    (hj : 0 < j) (hrange : t ≤ j*(j+1)) (x : ℚ) :
    ((jonesSumPolynomial (jonesConstant t) j).map (Int.castRingHom ℚ)).IsRoot x ↔
      x = -2 ∧ j = t := by
  constructor
  · intro h
    exact (root_magnitude _ t j ht ho rfl hj x h).resolve_right (by omega)
  · rintro ⟨rfl,rfl⟩
    have h := geometric_identity (jonesConstant j) j (-2)
    rw [pow_succ,ho.neg_pow] at h
    have hc := constant_eq j ho
    have he : (jonesSumPolynomial (jonesConstant j) j).eval (-2) = 0 := by
      zify at hc
      norm_num at h
      linarith
    change (Polynomial.map _ _).eval (-2) = 0
    have he' := congrArg (Int.castRingHom ℚ) he
    rw [←eval_map_apply] at he'
    simpa using he'

#print axioms jonesSumPolynomial_succ
#print axioms jonesSumPolynomial_shape
#print axioms jones_rational_root_iff

private lemma minus_two_degree {t j : ℕ} (ho : Odd t)
    (hr : (jonesSumPolynomial (jonesConstant t) j).eval (-2) = 0) : j = t := by
  have h := geometric_identity (jonesConstant t) j (-2)
  rw [hr,mul_zero,pow_succ] at h
  have hc := constant_eq t ho
  have he : (-2:ℤ)^j = -(2:ℤ)^t := by zify at hc; linarith
  have ha := congrArg Int.natAbs he
  simp only [Int.natAbs_pow,Int.natAbs_neg] at ha
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) ha

private lemma root_separation (t j : ℕ) (ht : Odd t) (hjt : j+5 ≤ 2*t)
    (z : ℂ) (hz : ((jonesSumPolynomial (jonesConstant t) j).map (Int.castRingHom ℂ)).IsRoot z) :
    Real.sqrt 2 < ‖z‖ := by
  let R := Real.sqrt 2
  have hs : R^2 = 2 := Real.sq_sqrt (by norm_num)
  have hR : 1 < R := by dsimp [R]; exact (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  by_contra! hle
  have hz' : (jonesConstant t : ℂ) + ∑ i ∈ Finset.range j, z^(i+1) = 0 := by
    change (Polynomial.map _ _).eval z = 0 at hz
    simpa [jonesSumPolynomial,Polynomial.map_sum,eval_finsetSum] using hz
  have hn := congrArg norm (eq_neg_of_add_eq_zero_left hz')
  rw [Complex.norm_natCast,norm_neg] at hn
  have hb : (jonesConstant t : ℝ) ≤ ∑ i ∈ Finset.range j, R^(i+1) := by
    rw [hn]
    refine (norm_sum_le ..).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hle _
  have hsum (k : ℕ) : (R-1)*(∑ i ∈ Finset.range k, R^(i+1)) = R*R^k-R := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ,pow_succ R k]
      linear_combination ih
  have hmass := mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hR.le)
  rw [hsum] at hmass
  have hpow : R^j*R^5 ≤ (2:ℝ)^t := by
    rw [←pow_add,←hs,←pow_mul]; exact pow_le_pow_right₀ hR.le hjt
  have hR5 : R^5 = 4*R := by linear_combination (R^3+2*R)*hs
  rw [hR5] at hpow
  have hc := constant_eq t ht
  have hc' : 3*(jonesConstant t : ℝ) = 2*((2:ℝ)^t+1) := by exact_mod_cast hc
  have hsmall : (3:ℝ) < 4*(R-1)*2 := by nlinarith [hs,sq_nonneg (R-1),hR]
  have haux := congrArg (fun y : ℝ => y*(R-1)) hc'
  have haux' := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 2*(R-1) by linarith)
  have hp := mul_lt_mul_of_pos_right hsmall (mul_pos (by linarith : 0 < R) (pow_pos (by linarith : 0 < R) j))
  nlinarith only [hp,haux',haux,hmass,hR]

private lemma root_product_gt (R : ℝ) (hR : 0 < R) (s : Multiset ℂ) (hne : s ≠ 0)
    (h : ∀ z ∈ s, R < ‖z‖) : R^s.card < ‖s.prod‖ := by
  induction s using Multiset.induction_on with
  | empty => contradiction
  | cons z s ih =>
    have hz := h z (Multiset.mem_cons_self ..)
    have hr : R^s.card ≤ ‖s.prod‖ := by
      by_cases hs : s = 0
      · simp [hs]
      · exact (ih hs (fun w hw => h w (Multiset.mem_cons_of_mem hw))).le
    rw [Multiset.card_cons,Multiset.prod_cons,norm_mul,pow_succ,mul_comm _ R]
    exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos hz hr hR.le ((pow_pos hR _).trans_le hr)

private lemma factor_degree_le_one (g : ℤ[X]) (hg : g.Monic)
    (hc : (g.coeff 0).natAbs ≤ 2) (hsep : ∀ z : ℂ, (g.map (Int.castRingHom ℂ)).IsRoot z →
      Real.sqrt 2 < ‖z‖) : g.natDegree ≤ 1 := by
  by_contra! hd
  let G := g.map (Int.castRingHom ℂ)
  have hm : G.Monic := hg.map _
  have hdeg : G.natDegree = g.natDegree := natDegree_map_eq_of_injective Int.cast_injective _
  have hcard := (IsAlgClosed.splits G).natDegree_eq_card_roots
  have hne : G.roots ≠ 0 := by intro h; rw [h,Multiset.card_zero] at hcard; omega
  have hp := root_product_gt _ (Real.sqrt_pos.mpr (by norm_num : 0 < (2:ℝ)))
    G.roots hne (fun z hz => hsep z (isRoot_of_mem_roots hz))
  have hn := congrArg norm (IsAlgClosed.splits G).coeff_zero_eq_leadingCoeff_mul_prod_roots
  simp only [hm.leadingCoeff,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul] at hn
  have hs : (2:ℝ) ≤ (Real.sqrt 2)^G.roots.card := by
    calc
      (2:ℝ) = (Real.sqrt 2)^2 := (Real.sq_sqrt (by norm_num)).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have hab : ‖G.coeff 0‖ ≤ 2 := by
    change ‖(g.map _).coeff 0‖ ≤ 2
    rw [coeff_map]
    change ‖(g.coeff 0 : ℂ)‖ ≤ 2
    rw [Complex.norm_intCast,←Int.cast_abs]
    rw [←Int.natCast_natAbs]
    exact_mod_cast hc
  linarith

/-- If the odd part of Jones's constant is prime, reducibility in this
initial degree range occurs exactly at his prescribed index. -/
theorem jones_irreducible_iff_in_range (t j : ℕ) (ht : 3 ≤ t) (ho : Odd t)
    (hp : ((2^t+1)/3).Prime) (hj : 2 ≤ j) (hjt : j+5 ≤ 2*t) :
    Irreducible ((jonesSumPolynomial (jonesConstant t) j).map (Int.castRingHom ℚ)) ↔ j ≠ t := by
  let f := jonesSumPolynomial (jonesConstant t) j
  have hdeg : f.natDegree = j := (jonesSumPolynomial_shape _ _).1
  have hm : f.Monic := (jonesSumPolynomial_shape _ _).2 (by omega)
  constructor
  · intro hi h
    have hr := (jones_rational_root_iff t j ht ho (by omega) (by nlinarith) (-2)).mpr ⟨rfl,h⟩
    have hd := natDegree_eq_of_degree_eq_some (degree_eq_one_of_irreducible_of_root hi hr)
    rw [natDegree_map_eq_of_injective Int.cast_injective] at hd
    change f.natDegree = 1 at hd
    omega
  · intro hne
    change Irreducible (f.map _)
    apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hm.isPrimitive).mp
    apply hm.irreducible_iff_natDegree.mpr
    refine ⟨fun h => by rw [h,natDegree_one] at hdeg; omega, ?_⟩
    intro a b ha hb hab
    have hconst : f.coeff 0 = jonesConstant t := by
      simp [f,jonesSumPolynomial,finsetSum_coeff,coeff_X_pow]
    let p := (2^t+1)/3
    have hmul : (a.coeff 0).natAbs*(b.coeff 0).natAbs = 2*p := by
      rw [←Int.natAbs_mul,←mul_coeff_zero,hab,hconst]
      rfl
    have small (g : ℤ[X]) (hg : g.Monic) (hdiv : g ∣ f) (hsmall : (g.coeff 0).natAbs ≤ 2) :
        g.natDegree = 0 := by
      have hs (z : ℂ) (hz : (g.map (Int.castRingHom ℂ)).IsRoot z) : Real.sqrt 2 < ‖z‖ :=
        root_separation t j ho hjt z (hz.dvd (Polynomial.map_dvd _ hdiv))
      have hd := factor_degree_le_one g hg hsmall hs
      by_contra hn
      have hlin := hg.eq_X_add_C (show g.natDegree = 1 by omega)
      have hroot : g.IsRoot (-(g.coeff 0)) := by
        change _ = 0
        conv_lhs => arg 2; rw [hlin]
        simp
      have hfroot := hroot.dvd hdiv
      change f.eval (-(g.coeff 0)) = 0 at hfroot
      have hpos : 0 < g.coeff 0 := by
        by_contra! he
        rw [show f = _ from rfl,sum_eval] at hfroot
        have hh : 0 ≤ ∑ i ∈ Finset.range j, (-(g.coeff 0))^(i+1) :=
          Finset.sum_nonneg fun _ _ => pow_nonneg (by omega) _
        have hlarge := hp.two_le
        unfold jonesConstant at hfroot
        omega
      have hnot : g.coeff 0 ≠ 1 := by
        intro he
        have hz : (g.map (Int.castRingHom ℂ)).IsRoot (-1) := by
          change _ = 0
          nth_rw 1 [hlin]
          simp [he]
        have hh := hs _ hz
        have hR := (Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 1)).mpr (by norm_num : (1:ℝ)^2 < 2)
        simp at hh
        linarith
      have he : g.coeff 0 = 2 := by omega
      rw [he] at hfroot
      exact hne (minus_two_degree ho hfroot)
    have hpd : p ∣ (a.coeff 0).natAbs*(b.coeff 0).natAbs := hmul ▸ dvd_mul_left p 2
    have bound {x y : ℕ} (hxy : x*y = 2*p) (hx : p ∣ x) : y ≤ 2 := by
      have hx0 : 0 < x := by by_contra! h; have hp' : 0 < p := hp.pos; nlinarith
      have hh := Nat.mul_le_mul_right y (Nat.le_of_dvd hx0 hx)
      by_contra! h
      have := Nat.mul_lt_mul_of_pos_left h hp.pos
      nlinarith
    rcases hp.dvd_mul.mp hpd with h|h
    · exact Or.inr (small b hb (hab ▸ dvd_mul_left _ _) (bound hmul h))
    · exact Or.inl (small a ha (hab ▸ dvd_mul_right _ _) (bound ((Nat.mul_comm ..).trans hmul) h))

#print axioms jones_irreducible_iff_in_range

end CunninghamChain
