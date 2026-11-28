import Mathlib
import research.arxiv.«1104.1579».CunninghamSelbergSieve

/-! Growth with chain length of the common Bateman–Horn constant. -/

namespace CunninghamChain

open Finset Filter Real BatemanHornConjecture
open scoped Topology

/-- Every odd prime with order of two below k divides this integer. -/
private def orderProduct (k : ℕ) : ℕ := ∏ i ∈ range k, (2^(i+1)-1)

private lemma orderProduct_pos (k : ℕ) : 0 < orderProduct k := by
  apply Finset.prod_pos
  intro i _
  have := one_lt_pow₀ (by decide : 1 < (2 : ℕ)) (by omega : i+1 ≠ 0)
  omega

private lemma orderProduct_factors (k : ℕ) : (orderProduct k).primeFactors.card ≤ k^2 := by
  have hprod : orderProduct k ≤ 2^(k^2) := calc
    orderProduct k ≤ ∏ _i ∈ range k, 2^k := by
      apply Finset.prod_le_prod'
      intro i hi
      exact (Nat.sub_le ..).trans (Nat.pow_le_pow_right (by decide) (by simpa using hi))
    _ = _ := by simp [← pow_mul, pow_two]
  have hlo : 2^(orderProduct k).primeFactors.card ≤ orderProduct k := calc
    _ = ∏ _p ∈ (orderProduct k).primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ (orderProduct k).primeFactors, p := Finset.prod_le_prod' fun _ hp =>
      (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ orderProduct k := Nat.le_of_dvd (orderProduct_pos k) (Nat.prod_primeFactors_dvd _)
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp (hlo.trans hprod)

private lemma small_order_mem {q k : ℕ} [Fact q.Prime] (hq : 2 < q)
    (h : orderOf (2 : ZMod q) < k) : q ∈ (orderProduct k).primeFactors := by
  let d := orderOf (2 : ZMod q)
  have hp : q.Prime := Fact.out
  have hz : (2 : ZMod q) ≠ 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff 2 q).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hq)
  have hd : 0 < d := orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
    ⟨q-1, by omega, ZMod.pow_card_sub_one_eq_one hz⟩)
  have hc : (2^d : ℕ) ≡ 1 [MOD q] := (ZMod.natCast_eq_natCast_iff ..).mp (by
    push_cast
    exact pow_orderOf_eq_one _)
  have hdvd : q ∣ 2^d-1 := (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mp hc.symm
  apply Nat.mem_primeFactors.mpr
  refine ⟨hp, hdvd.trans ?_, (orderProduct_pos k).ne'⟩
  unfold orderProduct
  have hi : d-1 ∈ range k := mem_range.mpr (by change d < k at h; omega)
  simpa [Nat.sub_add_cancel (by omega : 1 ≤ d)] using
    (Finset.dvd_prod_of_mem (f := fun i : ℕ => 2^(i+1)-1) hi)

/-- The primes above k² at which the local root count is below k have total
reciprocal mass at most one, uniformly in the truncation of the Euler product. -/
theorem chainForms_exceptional_reciprocal {k : ℕ} (hk : 2 ≤ k) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ k^2 < q ∧ OmegaP (chainForms 1 k) q < k) :
    ∑ q ∈ Q, (q : ℝ)⁻¹ ≤ 1 := by
  have hs : Q ⊆ (orderProduct k).primeFactors := by
    intro q hq
    obtain ⟨hp, hbig, hcount⟩ := hQ q hq
    let : Fact q.Prime := ⟨hp⟩
    have hq2 : 2 < q := by nlinarith
    rw [chainForms_omega_odd k q hq2] at hcount
    exact small_order_mem hq2 (by omega)
  have hcard := (Finset.card_le_card hs).trans (orderProduct_factors k)
  calc
    _ ≤ ∑ _q ∈ Q, ((k^2 : ℕ) : ℝ)⁻¹ := by
      apply sum_le_sum
      intro q hq
      apply inv_anti₀ (by positivity)
      exact_mod_cast (hQ q hq).2.1.le
    _ = (Q.card : ℝ) / ((k^2 : ℕ) : ℝ) := by simp [div_eq_mul_inv]
    _ ≤ 1 := (div_le_one (by positivity)).mpr (by exact_mod_cast hcard)

private lemma shifted_euler_bound (z : ℕ) {t : ℝ} (ht : 0 < t) :
    (∏ p ∈ z.primesLE, (1 - 1/(p : ℝ)^(1+t))⁻¹) ≤ ∑' n : ℕ, 1/(n : ℝ)^(1+t) := by
  let f : ℕ →* ℝ :=
    { toFun := fun n => 1/(n : ℝ)^(1+t)
      map_one' := by simp
      map_mul' := fun a b => by simp [Real.mul_rpow, Nat.cast_nonneg, div_eq_mul_inv, mul_comm] }
  have hf : Summable f := Real.summable_one_div_nat_rpow.mpr (by linarith)
  have he := EulerProduct.prod_primesBelow_geometric_eq_tsum_smoothNumbers (f := f) hf (z+1)
  have hs := hf.tsum_subtype_le f (z+1).smoothNumbers (fun n => (by dsimp [f]; positivity))
  exact he.trans_le hs

private lemma euler_shift_factor {p t : ℝ} (hp : 2 ≤ p) (ht : 0 < t) :
    (1 - 1/p)⁻¹ ≤ exp (2*t*(log p/p)) * (1 - 1/p^(1+t))⁻¹ := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 < p := by linarith
  have hbase : 0 < 1-1/p := sub_pos.mpr ((div_lt_one hp0).mpr hp1)
  have hpow : 1 < p^(1+t) := Real.one_lt_rpow hp1 (by linarith)
  have hshift : 0 < 1-1/p^(1+t) := sub_pos.mpr ((div_lt_one (by positivity)).mpr hpow)
  have hlog : 0 ≤ log p := Real.log_nonneg hp1.le
  have hid : 1/p^(1+t) = exp (-(log p*t))/p := by
    rw [rpow_add hp0, rpow_one, rpow_def_of_pos hp0, exp_neg]
    ring
  have hnum : 1 - exp (-(log p*t)) ≤ log p*t := by
    linarith [Real.add_one_le_exp (-(log p*t))]
  have hratio : (1-1/p^(1+t))/(1-1/p) ≤ 1+2*t*(log p/p) := by
    rw [hid, div_le_iff₀ hbase]
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hnum hp0.le,
      mul_nonneg (mul_nonneg hlog ht.le) (sub_nonneg.mpr hp)]
  have hh := hratio.trans (by linarith [Real.add_one_le_exp (2*t*(log p/p))] :
    1+2*t*(log p/p) ≤ exp (2*t*(log p/p)))
  rw [← div_eq_mul_inv, le_div_iff₀ hshift]
  simpa [div_eq_inv_mul] using hh

private lemma mertens_upper : ∀ᶠ z : ℕ in atTop,
    (∏ p ∈ z.primesLE, (1-1/(p:ℝ))⁻¹) ≤ (2*exp 4) * log z := by
  let t (z : ℕ) : ℝ := (log z)⁻¹
  have ht0 : Tendsto t atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hgt : ∀ᶠ z in atTop, 0 < t z := by
    filter_upwards [eventually_gt_atTop 1] with z hz
    exact inv_pos.mpr (log_pos (by exact_mod_cast hz))
  have hlim : Tendsto (fun z => 1+t z) atTop (𝓝[>] (1:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨by simpa using (tendsto_const_nhds (x := (1:ℝ))).add ht0,
      hgt.mono fun _ h => by simpa using h⟩
  have hzeta := (tendsto_sub_mul_tsum_nat_rpow.comp hlim).eventually (gt_mem_nhds (by norm_num : (1:ℝ)<2))
  filter_upwards [hgt,hzeta,eventually_gt_atTop 1] with z ht hzeta hz
  have hl : 0 < log z := log_pos (by exact_mod_cast hz)
  have hsum := sieve_sum_log_div_prime_le z (by omega) z.primesLE
    (fun p hp => ⟨Nat.prime_of_mem_primesLE hp, Nat.le_of_mem_primesLE hp⟩)
  have hs : ∑ p ∈ z.primesLE, 2*t z*(log p/p) ≤ 4 := by
    rw [← mul_sum]
    have h := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2*t z by positivity)
    dsimp only [t] at h ⊢
    field_simp [hl.ne'] at h ⊢
    linarith
  have hb : (∑' n : ℕ, 1/(n : ℝ)^(1+t z)) ≤ 2*log z := by
    change (1+t z-1)*(∑' n : ℕ, 1/(n : ℝ)^(1+t z)) < 2 at hzeta
    ring_nf at hzeta
    exact (div_le_iff₀ hl).mp (by simpa [t,div_eq_inv_mul,mul_comm] using hzeta.le)
  calc
    _ ≤ ∏ p ∈ z.primesLE, (exp (2*t z*(log p/p)) * (1-1/(p:ℝ)^(1+t z))⁻¹) := by
      apply Finset.prod_le_prod
      · intro p hp
        have h : (1:ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
        exact inv_nonneg.mpr (sub_nonneg.mpr ((div_le_one (by positivity)).mpr h.le))
      · intro p hp
        exact euler_shift_factor (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le) ht
    _ = exp (∑ p ∈ z.primesLE, 2*t z*(log p/p)) * ∏ p ∈ z.primesLE, (1-1/(p:ℝ)^(1+t z))⁻¹ := by
      rw [Finset.prod_mul_distrib, Real.exp_sum]
    _ ≤ exp 4 * (2*log z) := by
      have he := (shifted_euler_bound z ht).trans hb
      have hpos : 0 ≤ (∏ p ∈ z.primesLE, (1-1/(p:ℝ)^(1+t z))⁻¹) := by
        apply prod_nonneg
        intro p hp
        have hp1 : (1:ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
        have h := Real.one_lt_rpow hp1 (show 0 < 1+t z by linarith)
        exact inv_nonneg.mpr (sub_nonneg.mpr ((div_le_one (by positivity)).mpr h.le))
      exact mul_le_mul (Real.exp_le_exp.mpr hs) he hpos (exp_pos _).le
    _ = _ := by ring

private lemma roots_bounds {k p : ℕ} (hk : 2 ≤ k) (hp : p.Prime) :
    OmegaP (chainForms 1 k) p < p ∧ OmegaP (chainForms 1 k) p ≤ k := by
  by_cases h : p = 2
  · subst p
    rw [chainForms_omega_two (by omega)]
    omega
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 < p := by have := hp.two_le; omega
  rw [chainForms_omega_odd k p hp2]
  have hz : (2 : ZMod p) ≠ 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff 2 p).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hp2)
  have hd := Nat.le_of_dvd (by omega : 0 < p-1)
    (orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hz))
  omega

private noncomputable def primeLog (p : ℕ) : ℝ := -log (1-1/(p:ℝ))

private noncomputable def localLog (k p : ℕ) : ℝ :=
  k*primeLog p + log (1 - (OmegaP (chainForms 1 k) p : ℝ)/p)

private lemma base_pos {p : ℕ} (hp : p.Prime) : 0 < 1-1/(p:ℝ) :=
  sub_pos.mpr ((div_lt_one (by exact_mod_cast hp.pos)).mpr (by exact_mod_cast hp.one_lt))

private lemma root_factor_pos {k p : ℕ} (hk : 2 ≤ k) (hp : p.Prime) :
    0 < 1-(OmegaP (chainForms 1 k) p : ℝ)/p := by
  exact sub_pos.mpr ((div_lt_one (by exact_mod_cast hp.pos)).mpr
    (by exact_mod_cast (roots_bounds hk hp).1))

private lemma log_partial (k N : ℕ) (hk : 2 ≤ k) :
    log (BatemanHornPartialProduct (chainForms 1 k) N) =
      ∑ p ∈ N.primesBelow, localLog k p := by
  have hcard : (chainForms 1 k).card = k := by
    let F (i : ℕ) : Polynomial ℤ :=
      Polynomial.C ((2:ℤ)^i)*Polynomial.X + Polynomial.C (1*((2:ℤ)^i-1))
    have hlc (i : ℕ) : (F i).leadingCoeff = 2^i :=
      Polynomial.leadingCoeff_linear (by positivity)
    have hinj : Function.Injective F := by
      intro i j h
      have h' := congrArg Polynomial.leadingCoeff h
      rw [hlc,hlc] at h'
      exact (pow_right_injective₀ (by norm_num : (0:ℤ)<2) (by norm_num)) h'
    change ((range k).image F).card = k
    simp [card_image_of_injective _ hinj]
  unfold BatemanHornPartialProduct
  rw [Real.log_prod]
  · apply sum_congr rfl
    intro p hp
    have h := Nat.prime_of_mem_primesBelow hp
    rw [Real.log_mul (zpow_pos (base_pos h) _).ne' (root_factor_pos hk h).ne',
      hcard,Real.log_zpow]
    push_cast
    unfold localLog primeLog
    ring
  · intro p hp
    have h := Nat.prime_of_mem_primesBelow hp
    exact mul_ne_zero (zpow_pos (base_pos h) _).ne' (root_factor_pos hk h).ne'

private lemma primeLog_sum (z : ℕ) :
    ∑ p ∈ z.primesLE, primeLog p = log (∏ p ∈ z.primesLE, (1-1/(p:ℝ))⁻¹) := by
  rw [Real.log_prod (fun p hp => inv_ne_zero (base_pos (Nat.prime_of_mem_primesLE hp)).ne')]
  simp [primeLog]

private lemma local_small_upper {k p : ℕ} (hk : 2 ≤ k) (hp : p.Prime) :
    localLog k p ≤ k*primeLog p := by
  apply add_le_of_nonpos_right
  apply Real.log_nonpos (root_factor_pos hk hp).le
  exact sub_le_self _ (by positivity)

private lemma primeLog_upper {p : ℕ} (hp : p.Prime) : primeLog p ≤ 2*(p:ℝ)⁻¹ := by
  have h := Real.one_sub_inv_le_log_of_pos (base_pos hp)
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold primeLog
  have hb : (1-1/(p:ℝ))⁻¹-1 ≤ 2*(p:ℝ)⁻¹ := by
    rw [sub_le_iff_le_add, inv_le_iff_one_le_mul₀ (base_pos hp)]
    field_simp
    nlinarith
  linarith

private lemma local_regular_upper {k p : ℕ} (hk : 2 ≤ k) (hp : p.Prime)
    (h : OmegaP (chainForms 1 k) p = k) : localLog k p ≤ 0 := by
  have hpos := root_factor_pos hk hp
  rw [h] at hpos
  have hbern := one_add_le_pow_of_two_add_nonneg (a := -(1/(p:ℝ)))
    (by linarith [base_pos hp] : 0 ≤ 2 + -(1/(p:ℝ))) k
  have hh : 1-(k:ℝ)/p ≤ (1-1/(p:ℝ))^k := by
    simpa [sub_eq_add_neg,div_eq_mul_inv] using hbern
  have hl := Real.log_le_log hpos hh
  rw [Real.log_pow] at hl
  unfold localLog primeLog
  rw [h]
  linarith

private lemma finite_log_upper {k N : ℕ} (hk : 2 ≤ k) (hN : k^2 < N) :
    log (BatemanHornPartialProduct (chainForms 1 k) N) ≤
      k*log (∏ p ∈ (k^2).primesLE, (1-1/(p:ℝ))⁻¹) + 2*k := by
  let S := (k^2).primesLE
  let Q := N.primesBelow \ S
  let E := Q.filter fun p => OmegaP (chainForms 1 k) p < k
  have hs : S ⊆ N.primesBelow := fun p hp =>
    Nat.mem_primesBelow.mpr ⟨(Nat.le_of_mem_primesLE hp).trans_lt hN,Nat.prime_of_mem_primesLE hp⟩
  have hq (p) (hp : p ∈ Q) : p.Prime ∧ k^2 < p := by
    have hh := mem_sdiff.mp hp
    have hprime := Nat.prime_of_mem_primesBelow hh.1
    exact ⟨hprime,lt_of_not_ge fun hle => hh.2 (Nat.mem_primesLE.mpr ⟨hle,hprime⟩)⟩
  have hE := chainForms_exceptional_reciprocal hk E (fun p hp =>
    ⟨(hq _ (mem_filter.mp hp).1).1,(hq _ (mem_filter.mp hp).1).2,(mem_filter.mp hp).2⟩)
  have hQsum : ∑ p ∈ Q, localLog k p ≤ 2*k := calc
    _ ≤ ∑ p ∈ Q, if p ∈ E then (2*(k:ℝ))*(p:ℝ)⁻¹ else 0 := by
      apply sum_le_sum
      intro p hp
      split_ifs with he
      · have h := (local_small_upper hk (hq p hp).1).trans
          (mul_le_mul_of_nonneg_left (primeLog_upper (hq p hp).1) (Nat.cast_nonneg k))
        linarith
      · have hh := (roots_bounds hk (hq p hp).1).2
        apply local_regular_upper hk (hq p hp).1 (le_antisymm hh ?_)
        by_contra! hlt
        exact he (mem_filter.mpr ⟨hp,hlt⟩)
    _ = (2*k) * ∑ p ∈ E, (p:ℝ)⁻¹ := by
      rw [← sum_filter, ← mul_sum]
      congr 2
      ext p
      simp [E]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hE (show 0 ≤ 2*(k:ℝ) by positivity)]
  have hSsum : ∑ p ∈ S, localLog k p ≤ k*∑ p ∈ S, primeLog p := by
    rw [mul_sum]
    exact sum_le_sum fun p hp => local_small_upper hk (Nat.prime_of_mem_primesLE hp)
  rw [log_partial _ _ hk, ← primeLog_sum, ← sum_sdiff hs]
  linarith

private lemma mertens_lower (z : ℕ) :
    log ((z:ℝ)+1) ≤ ∏ p ∈ z.primesLE, (1-1/(p:ℝ))⁻¹ := by
  let f : ℕ →* ℝ :=
    { toFun := fun n => (n:ℝ)⁻¹
      map_one' := by simp
      map_mul' := by intros; simp [mul_comm] }
  have h {p : ℕ} (hp : p.Prime) : ‖f p‖ < 1 := by
    change ‖(p:ℝ)⁻¹‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  let I := Icc 1 z
  let e : I ↪ (z+1).smoothNumbers :=
    ⟨fun i => ⟨i, Nat.mem_smoothNumbers_of_lt (mem_Icc.mp i.2).1
      (Nat.lt_succ_of_le (mem_Icc.mp i.2).2)⟩, fun _ _ h =>
      Subtype.ext (congrArg (fun n : (z+1).smoothNumbers => (n:ℕ)) h)⟩
  have H := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := f) h (z+1)).2
  have hs := sum_le_hasSum (univ.map e) (fun _ _ => (by dsimp [f]; positivity)) H
  rw [sum_map] at hs
  change (∑ i : I, ((i:ℕ):ℝ)⁻¹) ≤ _ at hs
  rw [sum_coe_sort I (fun i => (i:ℝ)⁻¹)] at hs
  have hl := log_add_one_le_harmonic z
  rw [harmonic_eq_sum_Icc] at hl
  push_cast at hl
  simpa [f, Nat.primesLE, one_div] using hl.trans hs

private lemma local_small_lower {k p : ℕ} (hk : 2 ≤ k) (hp : p.Prime) :
    k*primeLog p - log p ≤ localLog k p := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hw : (OmegaP (chainForms 1 k) p : ℝ)+1 ≤ p := by
    exact_mod_cast (roots_bounds hk hp).1
  have hc : (p:ℝ)⁻¹ ≤ 1 - (OmegaP (chainForms 1 k) p : ℝ)/p := by
    rw [← one_div]
    field_simp
    linarith
  have hh := Real.log_le_log (inv_pos.mpr hp0) hc
  rw [Real.log_inv] at hh
  unfold localLog
  linarith

private lemma local_large_lower {k p : ℕ} (hk : 2 ≤ k) (hp : p.Prime) (hbig : 2*k < p) :
    -(2*(k:ℝ)^2) * ((p:ℝ)^2)⁻¹ ≤ localLog k p := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hkp : (2:ℝ)*k < p := by exact_mod_cast hbig
  let x : ℝ := (k:ℝ)/p
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hx2 : 2*x < 1 := by dsimp [x]; rw [← mul_div_assoc,div_lt_one hp0]; linarith
  have hx1 : 0 < 1-x := by linarith
  have hw : (OmegaP (chainForms 1 k) p : ℝ)/p ≤ x := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast (roots_bounds hk hp).2) hp0.le
  have hroot := Real.log_le_log hx1 (sub_le_sub_left hw 1)
  have hb := Real.log_le_sub_one_of_pos (base_pos hp)
  have hmain : x ≤ (k:ℝ)*primeLog p := by
    unfold primeLog x
    have hh := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α:=ℝ) k)
    simp only [div_eq_mul_inv, one_mul] at hh ⊢
    nlinarith
  have hinv : -x-2*x^2 ≤ 1-(1-x)⁻¹ := by
    have hh : (1-x)⁻¹ ≤ 1+x+2*x^2 := (inv_le_iff_one_le_mul₀ hx1).mpr (by
      nlinarith [mul_nonneg (sq_nonneg x) (by linarith : 0 ≤ 1-2*x)])
    linarith
  have hh := hinv.trans (Real.one_sub_inv_le_log_of_pos hx1)
  have hleft : -(2*(k:ℝ)^2)*((p:ℝ)^2)⁻¹ = -2*x^2 := by dsimp [x]; ring
  rw [hleft]
  unfold localLog
  linarith

private lemma tail_square_sum {m N : ℕ} (hm : 0 < m) (hN : m < N) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, m < p ∧ p < N) :
    ∑ p ∈ Q, ((p:ℝ)^2)⁻¹ ≤ (m:ℝ)⁻¹ := by
  let g (p : ℕ) : ℝ := -((p:ℝ)-1)⁻¹
  have hbound (p : ℕ) (hp : m < p) : ((p:ℝ)^2)⁻¹ ≤ g (p+1)-g p := by
    have hp1 : (1:ℝ) < p := by exact_mod_cast (by omega : 1 < p)
    have hpos : 0 < (p:ℝ)-1 := by linarith
    dsimp [g]
    push_cast
    rw [add_sub_cancel_right]
    field_simp
    nlinarith
  have hsub : Q ⊆ Ico (m+1) N := fun p hp => mem_Ico.mpr (hQ p hp)
  calc
    _ ≤ ∑ p ∈ Q, (g (p+1)-g p) := sum_le_sum fun p hp => hbound p (hQ p hp).1
    _ ≤ ∑ p ∈ Ico (m+1) N, (g (p+1)-g p) :=
      sum_le_sum_of_subset_of_nonneg hsub fun p hp _ =>
        (by positivity : 0 ≤ ((p:ℝ)^2)⁻¹).trans (hbound p (mem_Ico.mp hp).1)
    _ = g N - g (m+1) := sum_Ico_sub g hN
    _ ≤ _ := by
      have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
      dsimp [g]
      push_cast
      rw [add_sub_cancel_right]
      linarith [inv_nonneg.mpr (sub_nonneg.mpr hN1)]

private lemma finite_log_lower {k N : ℕ} (hk : 2 ≤ k) (hN : 2*k < N) :
    (k:ℝ)*log (log k) - (2*log 4+1)*k ≤ log (BatemanHornPartialProduct (chainForms 1 k) N) := by
  let S := (2*k).primesLE
  let Q := N.primesBelow \ S
  have hs : S ⊆ N.primesBelow := fun p hp =>
    Nat.mem_primesBelow.mpr ⟨(Nat.le_of_mem_primesLE hp).trans_lt hN,Nat.prime_of_mem_primesLE hp⟩
  have hq (p) (hp : p ∈ Q) : p.Prime ∧ 2*k < p ∧ p < N := by
    have hh := mem_sdiff.mp hp
    have hprime := Nat.prime_of_mem_primesBelow hh.1
    exact ⟨hprime,lt_of_not_ge fun hle => hh.2 (Nat.mem_primesLE.mpr ⟨hle,hprime⟩),
      (Nat.mem_primesBelow.mp hh.1).1⟩
  have htail := tail_square_sum (by omega) hN Q (fun p hp => (hq p hp).2)
  have hQsum : -(k:ℝ) ≤ ∑ p ∈ Q, localLog k p := calc
    _ = -(2*(k:ℝ)^2)*((2*k:ℕ):ℝ)⁻¹ := by push_cast; field_simp
    _ ≤ -(2*(k:ℝ)^2)*∑ p ∈ Q, ((p:ℝ)^2)⁻¹ :=
      mul_le_mul_of_nonpos_left htail (neg_nonpos.mpr (by positivity))
    _ ≤ _ := by
      rw [mul_sum]
      exact sum_le_sum fun p hp => local_large_lower hk (hq p hp).1 (hq p hp).2.1
  have hSsum : k*∑ p ∈ S, primeLog p - ∑ p ∈ S, log p ≤ ∑ p ∈ S, localLog k p := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_le_sum fun p hp => local_small_lower hk (Nat.prime_of_mem_primesLE hp)
  have hθ := Chebyshev.theta_le_log4_mul_x (x := (2*k:ℕ)) (by positivity)
  rw [Chebyshev.theta_eq_sum_primesLE_log] at hθ
  change ∑ p ∈ S, log p ≤ _ at hθ
  push_cast at hθ
  have hlog : log (log k) ≤ ∑ p ∈ S, primeLog p := by
    rw [primeLog_sum]
    apply Real.log_le_log (log_pos (by exact_mod_cast (show 1<k by omega)))
    exact (Real.log_le_log (by positivity) (by push_cast; linarith : (k:ℝ) ≤ ((2*k:ℕ):ℝ)+1)).trans
      (mertens_lower (2*k))
  rw [log_partial _ _ hk, ← sum_sdiff hs]
  nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α:=ℝ) k)]

/-- The Bateman–Horn constant for a length-k Cunningham prefix. -/
noncomputable def chainConstant (k : ℕ) : ℝ :=
  limUnder atTop (BatemanHornPartialProduct (chainForms 1 k))

/-- Both kinds have the same positive constant at each positive length. -/
theorem chainConstant_spec {k : ℕ} (hk : 0 < k) :
    0 < chainConstant k ∧
    Tendsto (BatemanHornPartialProduct (chainForms 1 k)) atTop (𝓝 (chainConstant k)) ∧
    Tendsto (BatemanHornPartialProduct (chainForms (-1) k)) atTop (𝓝 (chainConstant k)) := by
  obtain ⟨B,hB,hl⟩ := chainForms_positive_euler_limit k hk
  rw [chainConstant,hl.limUnder_eq]
  exact ⟨hB,hl,hl.congr fun n => chainForms_partialProduct_neg 1 k n⟩

/-- Uniform bounds in the length parameter, independent of any conjecture on
simultaneous prime values. -/
theorem chainConstant_log_bounds : ∀ᶠ k : ℕ in atTop,
    log (log k) - (2*log 4+1) ≤ log (chainConstant k)/k ∧
    log (chainConstant k)/k ≤ log (log k) + (6+log 4) := by
  obtain ⟨m,hm⟩ := eventually_atTop.mp mertens_upper
  filter_upwards [eventually_ge_atTop (max 2 m)] with k hk
  have hk2 : 2 ≤ k := (le_max_left ..).trans hk
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0<k by omega)
  have hl : 0 < log k := log_pos (by exact_mod_cast (show 1<k by omega))
  have hM := hm (k^2) (by have := (le_max_right 2 m).trans hk; nlinarith : m ≤ k^2)
  obtain ⟨hpos,hlim,_⟩ := chainConstant_spec (k:=k) (by omega)
  have hlog := (Real.continuousAt_log hpos.ne').tendsto.comp hlim
  constructor
  · apply (le_div_iff₀ hk0).mpr
    have h : (k:ℝ)*log (log k) - (2*log 4+1)*k ≤ log (chainConstant k) :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hlog
        (by filter_upwards [eventually_gt_atTop (2*k)] with n hn using finite_log_lower hk2 hn)
    linarith
  · apply (div_le_iff₀ hk0).mpr
    have h : log (chainConstant k) ≤
        k*log (∏ p ∈ (k^2).primesLE, (1-1/(p:ℝ))⁻¹) + 2*k :=
      le_of_tendsto_of_tendsto hlog tendsto_const_nhds
        (by filter_upwards [eventually_gt_atTop (k^2)] with n hn using finite_log_upper hk2 hn)
    have hp : 0 < ∏ p ∈ (k^2).primesLE, (1-1/(p:ℝ))⁻¹ :=
      prod_pos fun p hp => inv_pos.mpr (base_pos (Nat.prime_of_mem_primesLE hp))
    have hh := Real.log_le_log hp hM
    rw [Nat.cast_pow,Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    have hid : 2*exp 4*(2*log k) = 4*exp 4*log k := by ring
    rw [hid,Real.log_mul (by positivity) hl.ne', Real.log_mul (by norm_num) (exp_pos _).ne',
      Real.log_exp] at hh
    nlinarith [mul_le_mul_of_nonneg_left hh hk0.le]

open Asymptotics in
/-- The logarithm of the common constant is asymptotic to k log log k. -/
theorem chainConstant_log_asymptotic :
    (fun k : ℕ => log (chainConstant k)) ~[atTop] (fun k => (k:ℝ)*log (log k)) := by
  have ht : Tendsto (fun k : ℕ => log (log k)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hp := ht.eventually_gt_atTop 0
  have hlim (a : ℝ) : Tendsto (fun k : ℕ => a / log (log k)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := a)).mul (tendsto_inv_atTop_zero.comp ht)
  apply isEquivalent_of_tendsto_one
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun k : ℕ => 1-(2*log 4+1)/log (log k))
    (h := fun k : ℕ => 1+(6+log 4)/log (log k))
  · simpa using (tendsto_const_nhds (x := (1:ℝ))).sub (hlim (2*log 4+1))
  · simpa using (tendsto_const_nhds (x := (1:ℝ))).add (hlim (6+log 4))
  · filter_upwards [chainConstant_log_bounds,hp] with k hk hpos
    change _ ≤ log (chainConstant k)/((k:ℝ)*log (log k))
    rw [← div_div,le_div_iff₀ hpos]
    have := hk.1
    field_simp
    linarith
  · filter_upwards [chainConstant_log_bounds,hp] with k hk hpos
    change log (chainConstant k)/((k:ℝ)*log (log k)) ≤ _
    rw [← div_div,div_le_iff₀ hpos]
    have := hk.2
    field_simp
    linarith

#print axioms chainConstant_spec
#print axioms chainConstant_log_bounds
#print axioms chainConstant_log_asymptotic

#print axioms chainForms_exceptional_reciprocal

end CunninghamChain
