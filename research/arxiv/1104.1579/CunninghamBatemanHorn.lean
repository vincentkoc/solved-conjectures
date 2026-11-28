import FormalConjectures.Arxiv.«1104.1579».CunninghamChain
import FormalConjectures.Wikipedia.BatemanHornConjecture
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! Bateman–Horn local factors and exact-length counts for the two Cunningham recurrences. -/

namespace CunninghamChain

open Polynomial BatemanHornConjecture Filter Asymptotics
open scoped Topology

private noncomputable def chainForm (s : ℤ) (i : ℕ) : ℤ[X] :=
  C ((2 : ℤ) ^ i) * X + C (s * ((2 : ℤ) ^ i - 1))

/-- The first k affine forms, with s = 1 for the first kind and s = −1 for the second. -/
noncomputable def chainForms (s : ℤ) (k : ℕ) : Finset ℤ[X] := (Finset.range k).image (chainForm s)

private lemma form_lc (s : ℤ) (i : ℕ) : (chainForm s i).leadingCoeff = 2 ^ i :=
  leadingCoeff_linear (by positivity)

private lemma forms_card (s : ℤ) (k : ℕ) : (chainForms s k).card = k := by
  have hinj : Function.Injective (chainForm s) := by
    intro i j h
    have hh := congrArg leadingCoeff h
    simp only [form_lc] at hh
    exact (pow_right_injective₀ (by norm_num : (0 : ℤ) < 2) (by norm_num)) hh
  simp [chainForms, Finset.card_image_of_injective _ hinj]

private lemma form_bunyakovsky {s : ℤ} (hs : s = 1 ∨ s = -1) (i : ℕ) :
    BunyakovskyCondition (chainForm s i) := by
  have h2 : (2 : ℤ) ^ i ≠ 0 := by positivity
  refine ⟨(degree_linear h2).ge, irreducible_C_mul_X_add_C h2 ?_, ?_⟩
  · apply IsCoprime.isRelPrime
    refine ⟨1, -s, ?_⟩
    rcases hs with rfl | rfl <;> ring
  · rw [form_lc]
    positivity

private lemma mod_form (s : ℤ) (i q : ℕ) (z : ZMod q) :
    ((chainForm s i).map (Int.castRingHom (ZMod q))).eval z =
      2 ^ i * z + (s : ZMod q) * (2 ^ i - 1) := by
  simp [chainForm]

private lemma reflected_zero (s : ℤ) (i q : ℕ) (z : ZMod q) :
    ((chainForm (-s) i).map (Int.castRingHom (ZMod q))).eval (-z) =
      -((chainForm s i).map (Int.castRingHom (ZMod q))).eval z := by
  rw [mod_form, mod_form, Int.cast_neg]
  ring

/-- Negation bijects the forbidden residues, so both recurrences have identical
Bateman–Horn local root counts at every modulus. -/
theorem chainForms_omega_neg (s : ℤ) (k q : ℕ) :
    OmegaP (chainForms s k) q = OmegaP (chainForms (-s) k) q := by
  let bad (a : ℤ) := {z : ZMod q | ∃ f ∈ chainForms a k,
    (f.map (Int.castRingHom (ZMod q))).eval z = 0}
  have reflect (a : ℤ) (z : ZMod q) (hz : z ∈ bad a) : -z ∈ bad (-a) := by
    obtain ⟨f, hf, hzero⟩ := hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hf
    exact ⟨_, Finset.mem_image.mpr ⟨i, hi, rfl⟩, by rw [reflected_zero, hzero, neg_zero]⟩
  change (bad s).ncard = (bad (-s)).ncard
  apply Set.ncard_congr (fun z _ => -z) (fun z hz => reflect s z hz) (fun _ _ _ _ => neg_inj.mp)
  intro z hz
  exact ⟨-z, by simpa using reflect (-s) z hz, neg_neg _⟩

theorem chainForms_partialProduct_neg (s : ℤ) (k N : ℕ) :
    BatemanHornPartialProduct (chainForms s k) N =
    BatemanHornPartialProduct (chainForms (-s) k) N := by
  simp only [BatemanHornPartialProduct, forms_card]
  apply Finset.prod_congr rfl
  intro q _
  rw [chainForms_omega_neg s]

/-- At an odd prime, the forbidden residues repeat with the multiplicative
order of two, with no repetitions before that order. -/
theorem chainForms_omega_odd (k q : ℕ) [Fact q.Prime] (hq : 2 < q) :
    OmegaP (chainForms 1 k) q = min k (orderOf (2 : ZMod q)) := by
  classical
  let d := orderOf (2 : ZMod q)
  let root (i : ℕ) := ((2 : ZMod q) ^ i)⁻¹ - 1
  have htwo : (2 : ZMod q) ≠ 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff 2 q).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hq)
  have hd : 0 < d := orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
    ⟨q - 1, by omega, ZMod.pow_card_sub_one_eq_one htwo⟩)
  have hroot (i : ℕ) (z : ZMod q) :
      ((chainForm 1 i).map (Int.castRingHom (ZMod q))).eval z = 0 ↔ z = root i := by
    rw [mod_form]
    simp only [Int.cast_one, one_mul, root]
    field_simp [pow_ne_zero i htwo]
    constructor <;> intro h <;> linear_combination h
  have hset : {z : ZMod q | ∃ f ∈ chainForms 1 k, (f.map (Int.castRingHom (ZMod q))).eval z = 0} =
      ↑((Finset.range (min k d)).image root) := by
    ext z
    constructor
    · rintro ⟨f, hf, hz⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hf
      refine Finset.mem_image.mpr ⟨i % d, Finset.mem_range.mpr (lt_min (lt_of_le_of_lt
        (Nat.mod_le ..) (Finset.mem_range.mp hi)) (Nat.mod_lt _ hd)), ?_⟩
      rw [(hroot _ _).mp hz]
      dsimp only [root, d]
      rw [pow_mod_orderOf]
    · intro hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨_, Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le
        (min_le_left ..)), rfl⟩, (hroot ..).mpr rfl⟩
  rw [OmegaP, hset, Set.ncard_coe_finset, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj he
  have hi' := (Finset.mem_range.mp hi).trans_le (min_le_right ..)
  have hj' := (Finset.mem_range.mp hj).trans_le (min_le_right ..)
  apply (IsPrimitiveRoot.orderOf (2 : ZMod q)).pow_inj hi' hj'
  exact inv_injective (sub_left_inj.mp he)

/-- At two, only the initial form can vanish and it vanishes at zero. -/
theorem chainForms_omega_two {k : ℕ} (hk : 0 < k) : OmegaP (chainForms 1 k) 2 = 1 := by
  have hset : {z : ZMod 2 | ∃ f ∈ chainForms 1 k, (f.map (Int.castRingHom (ZMod 2))).eval z = 0} =
      {0} := by
    ext z
    constructor
    · rintro ⟨f, hf, hz⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
      rw [mod_form] at hz
      cases i with
      | zero => simpa using hz
      | succ i => simp [show (2 : ZMod 2) = 0 by decide] at hz
    · rintro rfl
      exact ⟨_, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hk, rfl⟩, by simp [chainForm]⟩
  rw [OmegaP, hset, Set.ncard_singleton]

private lemma omega_stable {k q : ℕ} [Fact q.Prime] (h2 : 2 < q) (hq : 2 ^ k < q) :
    OmegaP (chainForms 1 k) q = k := by
  rw [chainForms_omega_odd k q h2, min_eq_left]
  let d := orderOf (2 : ZMod q)
  by_contra! hd
  have hn : (2 : ZMod q) ≠ 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff 2 q).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) h2)
  have hpos : 0 < d := orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
    ⟨q - 1, by omega, ZMod.pow_card_sub_one_eq_one hn⟩)
  have hc : ((2 ^ d : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by
    push_cast
    exact pow_orderOf_eq_one _
  have hm := (ZMod.natCast_eq_natCast_iff ..).mp hc
  have hlt : 2 ^ d < q := lt_trans (Nat.pow_lt_pow_right (by decide) hd) hq
  change 2 ^ d % q = 1 % q at hm
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega)] at hm
  exact (one_lt_pow₀ (by decide : (1 : ℕ) < 2) hpos.ne').ne' hm

private lemma factor_bound (k : ℕ) {u : ℝ} (hu : 2 ≤ u) (hku : k ≤ u) :
    ‖(1 - 1 / u) ^ (-(k : ℤ)) * (1 - k / u) - 1‖ ≤ 2 * (k : ℝ) ^ 2 / u ^ 2 := by
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u - 1 := by linarith
  have ht : 0 < 1 - 1 / u := sub_pos.mpr ((div_lt_one hu0).mpr (by linarith))
  have hn : 0 ≤ 1 - k / u := sub_nonneg.mpr ((div_le_one hu0).mpr hku)
  have hber := one_add_le_pow_of_two_add_nonneg (a := -(1 / u)) (by linarith : 0 ≤ 2 + -(1 / u)) k
  have hber' : 1 - k / u ≤ (1 - 1 / u) ^ k := by simpa [sub_eq_add_neg, div_eq_mul_inv] using hber
  rw [zpow_neg, zpow_natCast, ← div_eq_inv_mul]
  have hupper := (div_le_one (pow_pos ht k)).mpr hber'
  rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hupper)]
  have hmul := mul_le_mul_of_nonneg_right
    (one_add_le_pow_of_two_add_nonneg (a := 1 / (u - 1)) (by positivity) k) hn
  have hid : 1 + 1 / (u - 1) = (1 - 1 / u)⁻¹ := by field_simp; ring
  rw [hid, inv_pow, ← div_eq_inv_mul] at hmul
  have hd : 1 - 2 * (k : ℝ) ^ 2 / u ^ 2 ≤ (1 + k * (1 / (u - 1))) * (1 - k / u) := by
    field_simp
    nlinarith [mul_nonneg (sq_nonneg (k : ℝ)) (show 0 ≤ u - 2 by linarith),
      mul_nonneg (Nat.cast_nonneg k) hu0.le]
  linarith

/-- The shared local product has a positive limit unconditionally. Its large
prime factors differ from one by at most 2k² / q². -/
theorem chainForms_positive_euler_limit (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (BatemanHornPartialProduct (chainForms 1 k)) atTop (𝓝 C) := by
  let F (q : ℕ) : ℝ := if q.Prime then
    (1 - 1 / (q : ℝ)) ^ (-(k : ℤ)) * (1 - (OmegaP (chainForms 1 k) q : ℝ) / q) else 1
  have hpos (q : ℕ) : 0 < F q := by
    dsimp only [F]
    split_ifs with hq
    · let : Fact q.Prime := ⟨hq⟩
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
      have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
      have ht : 0 < 1 - 1 / (q : ℝ) := sub_pos.mpr ((div_lt_one hq0).mpr hq1)
      apply mul_pos (zpow_pos ht _)
      apply sub_pos.mpr
      apply (div_lt_one hq0).mpr
      norm_cast
      by_cases h : q = 2
      · subst q
        rw [chainForms_omega_two hk]
        decide
      · have hq2 : 2 < q := lt_of_le_of_ne hq.two_le (Ne.symm h)
        rw [chainForms_omega_odd k q hq2]
        have hz : (2 : ZMod q) ≠ 0 := by
          exact_mod_cast (ZMod.natCast_eq_zero_iff 2 q).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hq2)
        exact (min_le_right ..).trans_lt ((Nat.le_of_dvd (by omega : 0 < q - 1)
          (orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hz))).trans_lt (by omega))
    · exact zero_lt_one
  have hs : Summable (fun q => F q - 1) := by
    apply Summable.of_norm_bounded_eventually_nat
      ((Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).mul_left (2 * (k : ℝ) ^ 2))
    filter_upwards [eventually_gt_atTop (2 ^ k), eventually_gt_atTop 2, eventually_ge_atTop k] with q hq hkq hqk
    dsimp only [F]
    split_ifs with hp
    · let : Fact q.Prime := ⟨hp⟩
      rw [omega_stable hkq hq]
      simpa [div_eq_mul_inv] using factor_bound k (u := (q : ℝ)) (by exact_mod_cast hkq.le) (by exact_mod_cast hqk)
    · simp only [sub_self, norm_zero, one_div]
      positivity
  have hl : Summable (fun q => Real.log (F q)) := by simpa using Real.summable_log_one_add_of_summable hs
  refine ⟨_, Real.exp_pos _, ((Real.hasProd_of_hasSum_log hpos hl.hasSum).tendsto_prod_nat).congr ?_⟩
  intro N
  simp [BatemanHornPartialProduct, Nat.primesBelow_eq_filter_range, Finset.prod_filter, F, forms_card]

private lemma forms_nonempty (s : ℤ) {k : ℕ} (hk : 0 < k) : (chainForms s k).Nonempty := by
  exact ⟨chainForm s 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hk, rfl⟩⟩

private lemma degrees_product (s : ℤ) (k : ℕ) : DegreesProduct (chainForms s k) = 1 := by
  apply Finset.prod_eq_one
  intro f hf
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
  apply natDegree_linear
  positivity

private lemma forms_compatible {s : ℤ} (hs : s = 1 ∨ s = -1) (k : ℕ) :
    SchinzelCondition (chainForms s k) := by
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨(-(s : ZMod p)).val, ?_⟩
  intro f hf hdiv
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
  have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr hdiv
  simp only [chainForm, eval_add, eval_mul, eval_C, eval_X, Int.cast_add, Int.cast_mul,
    Int.cast_pow, Int.cast_ofNat, Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_sub,
    Int.cast_one] at hc
  have : (s : ZMod p) = 0 := by linear_combination -hc
  rcases hs with rfl | rfl <;> norm_num at this

private lemma bh_prefix
    (hBH : type_of% BatemanHornConjecture.bateman_horn_conjecture) {s : ℤ}
    (hs : s = 1 ∨ s = -1) {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (BatemanHornPartialProduct (chainForms s k)) atTop (𝓝 C) ∧
      (fun x : ℝ => (CountSimultaneousPrimes (chainForms s k) x : ℝ)) ~[atTop]
        (fun x : ℝ => C * x / (Real.log x) ^ k) := by
  have hb := hBH (chainForms s k) (forms_nonempty s hk) (by
    rintro f hf
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
    exact form_bunyakovsky hs i) (forms_compatible hs k)
  simpa only [degrees_product, forms_card, Nat.cast_one, div_one] using hb

private lemma eval_first (p i : ℕ) : (chainForm 1 i).eval (p : ℤ) = firstKindTerm p i := by
  induction i with
  | zero => simp [chainForm, firstKindTerm]
  | succ i ih =>
    simp [chainForm] at ih
    simp only [chainForm, eval_add, eval_mul, eval_C, eval_X, firstKindTerm, pow_succ,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, one_mul]
    linear_combination 2 * ih

private lemma eval_second {p : ℕ} (hp : 0 < p) (i : ℕ) :
    (chainForm (-1) i).eval (p : ℤ) = secondKindTerm p i := by
  have hpos (j : ℕ) : 0 < secondKindTerm p j := by
    induction j with
    | zero => exact hp
    | succ j ih => simp only [secondKindTerm]; omega
  induction i with
  | zero => simp [chainForm, secondKindTerm]
  | succ i ih =>
    simp [chainForm] at ih
    simp only [chainForm, eval_add, eval_mul, eval_C, eval_X, secondKindTerm, pow_succ,
      Nat.cast_sub (by have := hpos i; omega : 1 ≤ 2 * secondKindTerm p i),
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, neg_one_mul]
    linear_combination 2 * ih

private noncomputable def prefixCount (t : ℕ → ℕ → ℕ) (k : ℕ) (x : ℝ) : ℕ := by
  classical exact ((Finset.range (⌊x⌋₊ + 1)).filter (fun p => ∀ i < k, (t p i).Prime)).card

/-- Number of natural seeds at most x satisfying the specified exact chain predicate. -/
noncomputable def exactChainCount (P : ℕ → ℕ → Prop) (k : ℕ) (x : ℝ) : ℕ := by
  classical exact ((Finset.range (⌊x⌋₊ + 1)).filter (fun p => P p k)).card

private lemma prefix_count_eq {s : ℤ} {t : ℕ → ℕ → ℕ} {k : ℕ} (hk : 0 < k)
    (hzero : t 0 0 = 0) (hev : ∀ p : ℕ, 0 < p → ∀ i, (chainForm s i).eval (p : ℤ) = t p i)
    (x : ℝ) : CountSimultaneousPrimes (chainForms s k) x = prefixCount t k x := by
  classical
  unfold CountSimultaneousPrimes prefixCount
  congr 1
  apply Finset.filter_congr
  intro p _
  by_cases hp : p = 0
  · subst p
    have hf : chainForm s 0 ∈ chainForms s k := Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hk, rfl⟩
    constructor
    · intro h
      have hh := h _ hf
      simp [chainForm] at hh
    · intro h
      have hh := h 0 hk
      simp [hzero] at hh
  · constructor
    · intro h i hi
      have ht := h (chainForm s i) (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩)
      simpa [hev p (Nat.pos_of_ne_zero hp)] using ht
    · rintro h f hf
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hf
      simpa [hev p (Nat.pos_of_ne_zero hp)] using h i (Finset.mem_range.mp hi)

private lemma count_partition {P : ℕ → ℕ → Prop} (t : ℕ → ℕ → ℕ) {k : ℕ}
    (he : ∀ p, P p k ↔ (∀ i < k, (t p i).Prime) ∧ ¬(t p k).Prime) (x : ℝ) :
    prefixCount t (k + 1) x + exactChainCount P k x = prefixCount t k x := by
  classical
  let s := (Finset.range (⌊x⌋₊ + 1)).filter (fun p => ∀ i < k, (t p i).Prime)
  have h := s.card_filter_add_card_filter_not (fun p => (t p k).Prime)
  have hs : s.filter (fun p => (t p k).Prime) =
      (Finset.range (⌊x⌋₊ + 1)).filter (fun p => ∀ i < k + 1, (t p i).Prime) := by
    ext p
    simp only [s, Finset.mem_filter, Nat.lt_succ_iff]
    constructor
    · rintro ⟨⟨hr, hb⟩, hl⟩
      exact ⟨hr, fun i hi => (hi.lt_or_eq.elim (hb i) (fun e => e ▸ hl))⟩
    · rintro ⟨hr, hp⟩
      exact ⟨⟨hr, fun i hi => hp i hi.le⟩, hp k le_rfl⟩
  have hstop : s.filter (fun p => ¬(t p k).Prime) =
      (Finset.range (⌊x⌋₊ + 1)).filter (fun p => P p k) := by
    ext p
    simp [s, he, and_assoc]
  rw [hs, hstop] at h
  exact h

private lemma longer_negligible {C D : ℝ} (hC : 0 < C) (k : ℕ) :
    (fun x : ℝ => D * x / (Real.log x) ^ (k + 1)) =o[atTop]
      (fun x : ℝ => C * x / (Real.log x) ^ k) := by
  apply isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx' : 0 < x := by linarith
    have hl := Real.log_pos hx
    exact fun h => False.elim ((by positivity : 0 < C * x / (Real.log x) ^ k).ne' h)
  · refine (tendsto_const_nhds (x := D / C) |>.div_atTop Real.tendsto_log_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx' : x ≠ 0 := by linarith
    have hl := (Real.log_pos hx).ne'
    rw [pow_succ]
    field_simp

private lemma bh_exact
    (hBH : type_of% BatemanHornConjecture.bateman_horn_conjecture) {s : ℤ}
    (hs : s = 1 ∨ s = -1) (t : ℕ → ℕ → ℕ) (P : ℕ → ℕ → Prop) {k : ℕ} (hk : 0 < k)
    (hzero : t 0 0 = 0) (hev : ∀ p : ℕ, 0 < p → ∀ i, (chainForm s i).eval (p : ℤ) = t p i)
    (he : ∀ p, P p k ↔ (∀ i < k, (t p i).Prime) ∧ ¬(t p k).Prime) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (BatemanHornPartialProduct (chainForms s k)) atTop (𝓝 C) ∧
      (fun x : ℝ => (exactChainCount P k x : ℝ)) ~[atTop]
        (fun x : ℝ => C * x / (Real.log x) ^ k) := by
  obtain ⟨C, hC, hlim, hbase⟩ := bh_prefix hBH hs hk
  obtain ⟨D, _, _, hnext⟩ := bh_prefix hBH hs (Nat.zero_lt_succ k)
  simp_rw [prefix_count_eq hk hzero hev] at hbase
  simp_rw [prefix_count_eq (Nat.zero_lt_succ k) hzero hev] at hnext
  refine ⟨C, hC, hlim, (hbase.sub_isLittleO (hnext.trans_isLittleO (longer_negligible hC k))).congr_left ?_⟩
  apply Eventually.of_forall
  intro x
  have h : (prefixCount t (k + 1) x : ℝ) + exactChainCount P k x = prefixCount t k x := by
    exact_mod_cast count_partition t he x
  dsimp
  linarith

/-- Bateman–Horn gives the same positive leading constant for the counts of
exact first-kind and second-kind chains at each fixed positive length. -/
theorem exact_counts_under_bateman_horn
    (hBH : type_of% BatemanHornConjecture.bateman_horn_conjecture) (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (BatemanHornPartialProduct (chainForms 1 k)) atTop (𝓝 C) ∧
      ((fun x : ℝ => (exactChainCount IsFirstKindChainOfLength k x : ℝ)) ~[atTop]
        (fun x : ℝ => C * x / (Real.log x) ^ k)) ∧
      ((fun x : ℝ => (exactChainCount IsSecondKindChainOfLength k x : ℝ)) ~[atTop]
        (fun x : ℝ => C * x / (Real.log x) ^ k)) := by
  obtain ⟨C, hC, hlim, hfirst⟩ := bh_exact hBH (Or.inl rfl) firstKindTerm IsFirstKindChainOfLength hk
    rfl (fun p _ => eval_first p) (fun _ => by simp [IsFirstKindChainOfLength, hk])
  obtain ⟨D, _, hother, hsecond⟩ := bh_exact hBH (Or.inr rfl) secondKindTerm IsSecondKindChainOfLength hk
    rfl (fun _ hp => eval_second hp) (fun _ => by simp [IsSecondKindChainOfLength, hk])
  have heq : BatemanHornPartialProduct (chainForms 1 k) = BatemanHornPartialProduct (chainForms (-1) k) :=
    funext (chainForms_partialProduct_neg 1 k)
  rw [← heq] at hother
  obtain rfl := tendsto_nhds_unique hlim hother
  exact ⟨C, hC, hlim, hfirst, hsecond⟩

#print axioms chainForms_positive_euler_limit
#print axioms chainForms_omega_odd
#print axioms chainForms_omega_two
#print axioms exact_counts_under_bateman_horn
#print axioms chainForms_omega_neg
#print axioms chainForms_partialProduct_neg

end CunninghamChain
