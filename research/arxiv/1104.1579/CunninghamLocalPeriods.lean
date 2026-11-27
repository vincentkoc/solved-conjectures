import FormalConjectures.Arxiv.«1104.1579».CunninghamChain
import Mathlib.NumberTheory.Fermat
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! Full-period divisibility tests and a quarter-seed bound for exact Cunningham chains of both kinds. -/

namespace CunninghamChain

/-- A full period of the multiplicative orbit meets 1 precisely when its
initial element belongs to the roots of unity of the period. -/
private theorem full_period_hits_one {K : Type*} [Field K] {z s : K} {d : ℕ}
    [NeZero d] (hz : IsPrimitiveRoot z d) :
    (∃ i < d, z ^ i * s = 1) ↔ s ^ d = 1 := by
  constructor
  · rintro ⟨i, _, he⟩
    have h := congrArg (fun x : K => x ^ d) he
    simpa only [mul_pow, ← pow_mul, Nat.mul_comm i d, pow_mul z d i, hz.pow_eq_one,
      one_pow, one_mul] using h
  · intro hs
    have hne : s ≠ 0 := by
      rintro rfl
      simp [NeZero.ne d] at hs
    obtain ⟨i, hi, he⟩ := hz.eq_pow_of_pow_eq_one (ξ := s⁻¹) (by rw [inv_pow, hs, inv_one])
    exact ⟨i, hi, by rw [he, inv_mul_cancel₀ hne]⟩

private theorem two_mod_ne_zero {q : ℕ} (hq : 2 < q) : (2 : ZMod q) ≠ 0 := by
  exact_mod_cast (ZMod.natCast_eq_zero_iff 2 q).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hq)

private theorem two_order_bounds {q : ℕ} [Fact q.Prime] (hq : 2 < q) :
    0 < orderOf (2 : ZMod q) ∧ orderOf (2 : ZMod q) ≤ q - 1 := by
  have h := ZMod.pow_card_sub_one_eq_one (two_mod_ne_zero hq)
  exact ⟨orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨q - 1, by omega, h⟩),
    Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one h)⟩

private theorem local_test {q : ℕ} [Fact q.Prime] (hq : 2 < q) (s : ZMod q)
    (t : ℕ → ℕ) (hz : ∀ i, q ∣ t i ↔ (2 : ZMod q) ^ i * s = 1) :
    (∃ i < orderOf (2 : ZMod q), q ∣ t i) ↔ s ^ orderOf (2 : ZMod q) = 1 := by
  have hpos := (two_order_bounds hq).1
  let : NeZero (orderOf (2 : ZMod q)) := ⟨hpos.ne'⟩
  simp_rw [hz]
  exact full_period_hits_one (IsPrimitiveRoot.orderOf (2 : ZMod q))

/-- Some first-kind term in a full period is divisible by q exactly when the
shifted seed has multiplicative order dividing the order of 2. -/
theorem firstKind_dvd_in_period_iff {q : ℕ} [Fact q.Prime] (hq : 2 < q) (p : ℕ) :
    (∃ i < orderOf (2 : ZMod q), q ∣ firstKindTerm p i) ↔
      ((p : ZMod q) + 1) ^ orderOf (2 : ZMod q) = 1 := by
  apply local_test hq
  intro i
  have hf : (firstKindTerm p i : ZMod q) + 1 = 2 ^ i * (p + 1) := by
    induction i with
    | zero => simp [firstKindTerm]
    | succ i ih =>
      simp only [firstKindTerm, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, pow_succ]
      linear_combination 2 * ih
  rw [← ZMod.natCast_eq_zero_iff, ← hf, add_eq_right]

/-- For a positive natural seed the second-kind test uses the shifted seed 1 − p. -/
theorem secondKind_dvd_in_period_iff {q : ℕ} [Fact q.Prime] (hq : 2 < q) (p : ℕ) (hp : 0 < p) :
    (∃ i < orderOf (2 : ZMod q), q ∣ secondKindTerm p i) ↔
      (1 - (p : ZMod q)) ^ orderOf (2 : ZMod q) = 1 := by
  apply local_test hq
  intro i
  have hp' (j : ℕ) : 0 < secondKindTerm p j := by
    induction j with
    | zero => exact hp
    | succ j ih => simp only [secondKindTerm]; omega
  have hf : 1 - (secondKindTerm p i : ZMod q) = 2 ^ i * (1 - p) := by
    induction i with
    | zero => simp [secondKindTerm]
    | succ i ih =>
      rw [secondKindTerm, Nat.cast_sub (by have := hp' i; omega : 1 ≤ 2 * secondKindTerm p i)]
      push_cast
      rw [pow_succ]
      linear_combination 2 * ih
  rw [← ZMod.natCast_eq_zero_iff, ← hf, sub_eq_self]

private theorem short_prefix {q k : ℕ} [Fact q.Prime] (hq : 2 < q) (t : ℕ → ℕ)
    (hbig : ∀ i, q < t i) (hprime : ∀ i < k, (t i).Prime)
    (hit : ∃ i < orderOf (2 : ZMod q), q ∣ t i) : k + 1 < q := by
  obtain ⟨i, hi, hdiv⟩ := hit
  have hki : k ≤ i := by
    by_contra! h
    exact (hbig i).ne ((Nat.prime_dvd_prime_iff_eq Fact.out (hprime i h)).mp hdiv)
  have := (two_order_bounds hq).2
  omega

private theorem first_short {p q k : ℕ} [Fact q.Prime] (hq : 2 < q) (hqp : q < p)
    (hc : IsFirstKindChainOfLength p k)
    (hs : ((p : ZMod q) + 1) ^ orderOf (2 : ZMod q) = 1) : k + 1 < q := by
  apply short_prefix hq _ _ hc.2.1 ((firstKind_dvd_in_period_iff hq p).mpr hs)
  intro i
  induction i with
  | zero => exact hqp
  | succ i ih => simp only [firstKindTerm]; omega

private theorem second_short {p q k : ℕ} [Fact q.Prime] (hq : 2 < q) (hqp : q < p)
    (hc : IsSecondKindChainOfLength p k)
    (hs : (1 - (p : ZMod q)) ^ orderOf (2 : ZMod q) = 1) : k + 1 < q := by
  apply short_prefix hq _ _ hc.2.1 ((secondKind_dvd_in_period_iff hq p (by omega)).mpr hs)
  intro i
  induction i with
  | zero => exact hqp
  | succ i ih => simp only [secondKindTerm]; omega

private theorem power_in_period {q : ℕ} (n : ℕ) :
    ((2 : ZMod q) ^ n) ^ orderOf (2 : ZMod q) = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]

/-- Write an odd a ≥ 5 as a power of two plus a small odd remainder exceeding one. -/
private theorem split_odd_core {a : ℕ} (ha : 5 ≤ a) (hodd : Odd a) :
    ∃ j m : ℕ, 1 < m ∧ Odd m ∧ 2 * m ≤ a + 1 ∧ a = 2 ^ j + m := by
  let j := (a - 2).log2
  have hlow : 2 ^ j ≤ a - 2 := Nat.log2_self_le (by omega)
  have hhigh : a - 2 < 2 ^ j * 2 := by simpa only [pow_succ] using (Nat.lt_log2_self (n := a - 2))
  have hj : 1 ≤ j := (Nat.le_log2 (by omega : a - 2 ≠ 0)).mpr (by norm_num; omega)
  obtain ⟨v, hv⟩ := (even_two : Even (2 : ℕ)).pow_of_ne_zero (by omega : j ≠ 0)
  obtain ⟨w, hw⟩ := hodd
  exact ⟨j, a - 2 ^ j, by omega, ⟨w - v, by omega⟩, by omega, by omega⟩

private theorem odd_factor {m : ℕ} (hm : 1 < m) (ho : Odd m) :
    ∃ q : ℕ, q.Prime ∧ 2 < q ∧ q ∣ m ∧ q ≤ m := by
  obtain ⟨q, hq, hdiv⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  have h2 : q ≠ 2 := by rintro rfl; exact ho.not_two_dvd_nat hdiv
  exact ⟨q, hq, lt_of_le_of_ne hq.two_le h2.symm, hdiv, Nat.le_of_dvd (by omega) hdiv⟩

private theorem factor_even {x : ℕ} (hpos : 0 < x) (he : Even x) :
    ∃ e a : ℕ, Odd a ∧ x = 2 ^ e * a ∧ 2 * a ≤ x := by
  obtain ⟨e, a, ho, heq⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
  have he0 : e ≠ 0 := by
    rintro rfl
    simp only [pow_zero, one_mul] at heq
    exact (Nat.not_even_iff_odd.mpr ho) (heq ▸ he)
  have hpow : 2 ≤ 2 ^ e := (Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ e by omega))
  exact ⟨e, a, ho, heq, heq ▸ Nat.mul_le_mul_right a hpow⟩

private theorem first_quarter_large {p k : ℕ} (hbig : 40 < p) (hc : IsFirstKindChainOfLength p k) :
    4 * k < p := by
  have hp : p.Prime := hc.2.1 0 hc.1
  have ho := hp.odd_of_ne_two (by omega)
  obtain ⟨e, a, ha, he, hle⟩ := factor_even (Nat.zero_lt_succ p) (by
    obtain ⟨m, hm⟩ := ho; exact ⟨m + 1, by omega⟩)
  by_cases hsmall : a < 5
  · let : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hcast : ((p : ZMod 5) + 1) = 2 ^ e * (a : ZMod 5) := by
      simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_zero,
        zero_add, one_add_one_eq_two] using
        congrArg (fun n : ℕ => (n : ZMod 5)) he
    have hn : (a : ZMod 5) ≠ 0 := by
      apply (ZMod.natCast_eq_zero_iff a 5).not.mpr
      obtain ⟨v,hv⟩ := ha
      exact Nat.not_dvd_of_pos_of_lt (by omega) hsmall
    have hroot : IsPrimitiveRoot (2 : ZMod 5) 4 := IsPrimitiveRoot.mk_of_lt _ (by decide)
      (by decide) (by intro i hi hi'; interval_cases i <;> decide)
    have := first_short (q := 5) (by decide) (by omega) hc (by
      rw [← hroot.eq_orderOf, hcast]
      exact ZMod.pow_card_sub_one_eq_one (mul_ne_zero (pow_ne_zero _ (by decide)) hn))
    omega
  · obtain ⟨j, m, hm, hodd, hbound, heq⟩ := split_odd_core (by omega) ha
    obtain ⟨q, hq, hq2, hd, hqm⟩ := odd_factor hm hodd
    let : Fact q.Prime := ⟨hq⟩
    have hcast : ((p : ZMod q) + 1) = 2 ^ e * (a : ZMod q) := by
      simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_zero,
        zero_add, one_add_one_eq_two] using
        congrArg (fun n : ℕ => (n : ZMod q)) he
    have hz := (ZMod.natCast_eq_zero_iff m q).mpr hd
    have hseed : ((p : ZMod q) + 1) = 2 ^ (e + j) := by
      rw [hcast, heq, Nat.cast_add, hz, add_zero, Nat.cast_pow, Nat.cast_ofNat, pow_add]
    have := first_short hq2 (by omega) hc (by rw [hseed]; exact power_in_period _)
    omega

private theorem two_primitive_eleven : IsPrimitiveRoot (2 : ZMod 11) 10 :=
  IsPrimitiveRoot.mk_of_lt _ (by decide) (by decide)
    (by intro i hi hi'; interval_cases i <;> decide)

private theorem second_short_of_core {p k a e q : ℕ} [Fact q.Prime]
    (hq : 2 < q) (hqp : q < p) (hc : IsSecondKindChainOfLength p k)
    (he : p = 2 ^ e * a + 1) (j : ℕ) (hd : q ∣ a + 2 ^ j) : k + 1 < q := by
  have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  push_cast at hz
  apply second_short hq hqp hc
  have hs : 1 - (p : ZMod q) = 2 ^ (e + j) := by
    rw [he, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat, pow_add]
    linear_combination -(2 : ZMod q) ^ e * hz
  rw [hs]
  exact power_in_period _

private theorem second_quarter_large {p k : ℕ} (hbig : 40 < p) (hc : IsSecondKindChainOfLength p k) :
    4 * k < p := by
  by_contra! hlong
  have hp : p.Prime := hc.2.1 0 hc.1
  obtain ⟨r, hr⟩ := hp.odd_of_ne_two (by omega)
  obtain ⟨e, a, ha, he, hle⟩ := factor_even (show 0 < p - 1 by omega) (show Even (p - 1) from ⟨r, by omega⟩)
  have he' : p = 2 ^ e * a + 1 := by omega
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (a + 1) with ⟨j, hj⟩ | ⟨q, hq, hd, ho⟩
  · let : Fact (Nat.Prime 11) := ⟨by decide⟩
    have hzero : (a : ZMod 11) = 0 := by
      by_contra hne
      have hs : 1 - (p : ZMod 11) = -(2 ^ e * (a : ZMod 11)) := by
        rw [he']; push_cast; ring
      have := second_short (q := 11) (by decide) (by omega) hc (by
        rw [← two_primitive_eleven.eq_orderOf, hs]
        exact ZMod.pow_card_sub_one_eq_one (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (by decide)) hne)))
      omega
    have hj5 : 5 ∣ j := by
      apply dvd_trans (by decide : 5 ∣ 10)
      apply two_primitive_eleven.dvd_of_pow_eq_one
      have hh := congrArg (fun n : ℕ => (n : ZMod 11)) hj
      simpa [hzero] using hh.symm
    have hj0 : j ≠ 0 := by
      intro h; rw [h, pow_zero] at hj; obtain ⟨b, hb⟩ := ha; omega
    have hcomp : ¬ (a + 2).Prime := by
      intro hp'
      have hfermat : (2 ^ j + 1).Prime := by rwa [← hj]
      obtain ⟨m, hm⟩ := Nat.pow_of_pow_add_prime (by decide : 1 < 2) hj0 hfermat
      have := (by decide : Nat.Prime 5).dvd_of_dvd_pow (hm ▸ hj5)
      norm_num at this
    let q := (a + 2).minFac
    have hq : q.Prime := Nat.minFac_prime (by omega)
    have hd : q ∣ a + 2 := Nat.minFac_dvd _
    have hq2 : 2 < q := by
      obtain ⟨b, hb⟩ := ha
      have := hq.two_le
      by_contra! hh
      have heq : q = 2 := by omega
      rw [heq] at hd
      omega
    have hsq : q ^ 2 ≤ a + 2 := Nat.minFac_sq_le_self (by omega) hcomp
    have hqa : 2 * q ≤ a + 2 := le_trans (by nlinarith : 2 * q ≤ q ^ 2) hsq
    let : Fact q.Prime := ⟨hq⟩
    have := second_short_of_core hq2 (by omega) hc he' 1 (by simpa using hd)
    omega
  · have hq2 := lt_of_le_of_ne hq.two_le (show 2 ≠ q by intro h; subst q; exact (by decide : ¬Odd 2) ho)
    obtain ⟨b, hb⟩ := ha
    have hd' : q ∣ b + 1 := by
      have hd'' : q ∣ (b + 1) * 2 := by rwa [show (b + 1) * 2 = a + 1 by omega]
      exact (hq.dvd_mul.mp hd'').resolve_right (Nat.not_dvd_of_pos_of_lt (by decide) hq2)
    have hqb := Nat.le_of_dvd (by omega) hd'
    let : Fact q.Prime := ⟨hq⟩
    have := second_short_of_core hq2 (by omega) hc he' 0 (by simpa using hd)
    omega

private theorem check_small_lengths (t : ℕ → ℕ → ℕ) (bad : Finset (ℕ × ℕ))
    (table : ∀ x : Fin 41, x.val.Prime → ∃ j : Fin 6,
      (∀ i : Fin j.val, (t x.val i.val).Prime) ∧ ¬(t x.val j.val).Prime ∧
        (x.val ≤ 4 * j.val ↔ (x.val, j.val) ∈ bad))
    {p k : ℕ} (hsmall : p ≤ 40) (hp : p.Prime)
    (hpre : ∀ i < k, (t p i).Prime) (hstop : ¬(t p k).Prime) :
    p ≤ 4 * k ↔ (p, k) ∈ bad := by
  obtain ⟨j, hbefore, hafter, hclass⟩ := table ⟨p, by omega⟩ hp
  have he : k = j.val := le_antisymm
    (le_of_not_gt fun h => hafter (hpre _ h))
    (le_of_not_gt fun h => hstop (hbefore ⟨k, h⟩))
  exact he ▸ hclass

/-- These four exact first-kind chains are all the exceptions to k < p/4. -/
theorem firstKind_quarter_exceptions (p k : ℕ) :
    (IsFirstKindChainOfLength p k ∧ p ≤ 4 * k) ↔
      (p, k) ∈ ({(2, 5), (3, 2), (5, 4), (11, 3)} : Finset (ℕ × ℕ)) := by
  constructor
  · rintro ⟨hc, hlong⟩
    by_cases h : p ≤ 40
    · exact (check_small_lengths firstKindTerm _ (by decide) h (hc.2.1 0 hc.1) hc.2.1 hc.2.2).mp hlong
    · exact (not_lt_of_ge hlong (first_quarter_large (by omega) hc)).elim
  · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      refine ⟨⟨by decide, ?_, by decide⟩, by decide⟩ <;> intro i hi <;> interval_cases i <;> decide

set_option maxRecDepth 4096 in
/-- These three exact second-kind chains are all the exceptions to k < p/4. -/
theorem secondKind_quarter_exceptions (p k : ℕ) :
    (IsSecondKindChainOfLength p k ∧ p ≤ 4 * k) ↔
      (p, k) ∈ ({(2, 3), (3, 2), (7, 2)} : Finset (ℕ × ℕ)) := by
  constructor
  · rintro ⟨hc, hlong⟩
    by_cases h : p ≤ 40
    · exact (check_small_lengths secondKindTerm _ (by decide) h (hc.2.1 0 hc.1) hc.2.1 hc.2.2).mp hlong
    · exact (not_lt_of_ge hlong (second_quarter_large (by omega) hc)).elim
  · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      refine ⟨⟨by decide, ?_, by decide⟩, by decide⟩ <;> intro i hi <;> interval_cases i <;> decide

#print axioms firstKind_quarter_exceptions
#print axioms secondKind_quarter_exceptions
#print axioms firstKind_dvd_in_period_iff
#print axioms secondKind_dvd_in_period_iff

end CunninghamChain
