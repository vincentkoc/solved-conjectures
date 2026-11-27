import Green33ReflectionRigidity
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-! Power sums for extremal cyclic two-bases at prime moduli. The moment argument adapts
Dongryul Kim's method for perfect Lee codes (arXiv:1701.08412) to the extremal sumset profile. -/

open Finset Polynomial Green33Multiplicity Green33ReflectionRigidity
open scoped Pointwise

namespace Green33PrimeMoments

/-- If all entries are nonzero and the length is nonzero in the field, a positive
power sum of degree at most the length is nonzero. Evaluate the root polynomial
at each entry, then compare its constant term. -/
private lemma exists_nonzero_moment {ι K : Type*} [Field K] (A : Finset ι) (v : ι → K)
    (hk : (A.card : K) ≠ 0) (hv : ∀ a ∈ A, v a ≠ 0) :
    ∃ r ∈ Icc 1 A.card, ∑ a ∈ A, v a ^ r ≠ 0 := by
  classical
  by_contra! h
  let P : K[X] := ∏ a ∈ A, (X - C (v a))
  have hd : P.natDegree = A.card := natDegree_finsetProd_X_sub_C_eq_card _ _
  have hzero (a : ι) (ha : a ∈ A) : P.eval (v a) = 0 := by
    simp only [P, eval_prod, eval_sub, eval_X, eval_C]
    exact prod_eq_zero ha (sub_self _)
  have hconst : P.eval 0 ≠ 0 := by
    simp only [P, eval_prod, eval_sub, eval_X, eval_C, zero_sub]
    exact prod_ne_zero_iff.mpr fun a ha => neg_ne_zero.mpr (hv a ha)
  have hs : ∑ a ∈ A, P.eval (v a) = (A.card : K) * P.eval 0 := by
    conv_lhs => arg 2; ext a; rw [eval_eq_sum_range, hd]
    rw [sum_comm, sum_eq_single 0]
    · simp [coeff_zero_eq_eval_zero]
    · intro j hj hj0
      rw [← mul_sum, h j (mem_Icc.mpr ⟨by omega, by simpa using mem_range.mp hj⟩), mul_zero]
    · simp
  rw [sum_eq_zero hzero] at hs
  exact (mul_ne_zero hk hconst) hs.symm

/-- The endpoint terms determine the pair moment when all interior products vanish. -/
theorem pair_moment_endpoints {ι K : Type*} [Field K] (A : Finset ι) (v : ι → K)
    (r : ℕ) (hr : 0 < r) (h : ∀ j, 0 < j → j < r →
      (∑ a ∈ A, v a ^ j) * (∑ a ∈ A, v a ^ (r - j)) = 0) :
    ∑ a ∈ A, ∑ b ∈ A, (v a + v b) ^ r = 2 * (A.card : K) * ∑ a ∈ A, v a ^ r := by
  let P (j : ℕ) := ∑ a ∈ A, v a ^ j
  have expand : ∑ a ∈ A, ∑ b ∈ A, (v a + v b) ^ r =
      ∑ j ∈ range (r + 1), P j * P (r - j) * (r.choose j : K) := by
    simp only [add_pow]
    calc
      _ = ∑ a ∈ A, ∑ j ∈ range (r + 1), ∑ b ∈ A,
            v a ^ j * v b ^ (r - j) * (r.choose j : K) :=
        sum_congr rfl fun _ _ => sum_comm
      _ = _ := by
        rw [sum_comm]
        simp only [P, sum_mul, mul_sum, mul_assoc]
        exact sum_congr rfl fun _ _ => sum_comm
  rw [expand, sum_range_succ, sum_eq_single 0]
  · simp [P]; ring
  · intro j hj hj0
    rw [show P j * P (r - j) = 0 from h j (Nat.pos_of_ne_zero hj0) (mem_range.mp hj), zero_mul]
  · exact fun hh => (hh (mem_range.mpr hr)).elim

private lemma weight_fibers {ι K : Type*} [Fintype K] [Field K] (B : Finset ι)
    (f : ι → K) (w : K → K) [DecidableEq K] :
    ∑ t, (((B.filter fun a => f a = t).card : K) * w t) = ∑ a ∈ B, w (f a) := by
  classical
  simp only [card_eq_sum_ones, Nat.cast_sum, sum_mul, sum_filter]
  rw [sum_comm]
  simp

/-- A centered moment identity obtained by weighting the extremal representation profile. -/
theorem extremal_moment {p : ℕ} [Fact p.Prime] (A : Finset (ZMod p))
    (s : ZMod p) (hoff : ∀ t ≠ s, reps A t + diagonalReps A t = 2)
    (r : ℕ) (hr : 0 < r) (hlt : r < p - 1) :
    (∑ a ∈ A, ∑ b ∈ A, ((2 * a - s) + (2 * b - s)) ^ r) +
      2 ^ r * (∑ a ∈ A, (2 * a - s) ^ r) = 0 := by
  classical
  let w (t : ZMod p) := (2 * (t - s)) ^ r
  have hsum : ∑ t, w t = 0 := by
    have ht : ∑ t : ZMod p, (t - s) ^ r = ∑ t : ZMod p, t ^ r :=
      Fintype.sum_equiv (Equiv.subRight s) _ _ (fun _ => rfl)
    have h := FiniteField.sum_pow_lt_card_sub_one (ZMod p) r (by simpa using hlt)
    simp [w, mul_pow, ← mul_sum, ht, h]
  have hw : ∑ t, ((reps A t : ZMod p) + diagonalReps A t) * w t = 0 := by
    calc
      _ = ∑ t, 2 * w t := by
        apply sum_congr rfl
        intro t _
        by_cases hs : t = s
        · simp [hs, w, hr.ne']
        · rw [← Nat.cast_add, hoff t hs]; norm_num
      _ = 0 := by rw [← mul_sum, hsum, mul_zero]
  have hadd (a b : ZMod p) : w (a + b) = ((2 * a - s) + (2 * b - s)) ^ r := by
    dsimp [w]; ring
  have hd (a : ZMod p) : w (a + a) = 2 ^ r * (2 * a - s) ^ r := by
    rw [← mul_pow]; dsimp [w]; ring
  simp only [add_mul, sum_add_distrib, reps, diagonalReps, weight_fibers, sum_product] at hw
  conv at hw => lhs; rhs; arg 2; ext a; rw [hd]
  simpa only [hadd, mul_sum] using hw

/-- At prime order `2m²+1`, an extremal cyclic two-basis of size `2m` forces
`−m` to occur among the powers of four of exponents `0, …, m−1`. -/
theorem power_of_four_necessary (p m : ℕ) [Fact p.Prime] (hm : 1 < m)
    (hp : p = 2 * m ^ 2 + 1) (A : Finset (ZMod p)) (hA : A + A = univ)
    (hk : A.card = 2 * m) : ∃ i < m, (4 : ZMod p) ^ i = -(m : ZMod p) := by
  classical
  have hlt : A.card < p - 1 := by
    rw [hk, hp, Nat.add_sub_cancel]
    nlinarith [Nat.mul_le_mul_left m (show 2 ≤ m by omega)]
  have hchar (j : ℕ) (hj : 0 < j) (hjp : j < p) : (j : ZMod p) ≠ 0 := by
    exact fun h => (Nat.le_of_dvd hj ((ZMod.natCast_eq_zero_iff j p).mp h)).not_gt hjp
  have hk0 : (A.card : ZMod p) ≠ 0 := hchar _ (by omega) (by omega)
  have h₂ : (2 : ZMod p) ≠ 0 := hchar 2 (by decide) (by omega)
  have heq : 2 * Fintype.card (ZMod p) = A.card ^ 2 + 2 := by rw [ZMod.card, hk, hp]; ring
  obtain ⟨s, href, hd, hoff⟩ := extremal_profile A hA heq
  let v (a : ZMod p) := 2 * a - s
  have hv (a : ZMod p) (ha : a ∈ A) : v a ≠ 0 := by
    intro h
    have he : a + a = s := by simpa [v, two_mul] using sub_eq_zero.mp h
    have hf : a ∈ A.filter (fun b => b + b = s) := mem_filter.mpr ⟨ha, he⟩
    exact (card_pos.mpr ⟨a, hf⟩).ne' hd
  let P (j : ℕ) := ∑ a ∈ A, v a ^ j
  have hex : ∃ j, j ∈ Icc 1 A.card ∧ P j ≠ 0 := exists_nonzero_moment A v hk0 hv
  let r := Nat.find hex
  obtain ⟨hmem, hP⟩ := Nat.find_spec hex
  change r ∈ Icc 1 A.card at hmem
  change P r ≠ 0 at hP
  obtain ⟨hr, hrk⟩ := mem_Icc.mp hmem
  have hsmall (j : ℕ) (hj : 0 < j) (hjr : j < r) : P j = 0 := by
    by_contra h
    exact Nat.find_min hex hjr ⟨mem_Icc.mpr ⟨hj, by omega⟩, h⟩
  have hcoeff : (2 : ZMod p) * A.card + 2 ^ r = 0 := by
    have hw := extremal_moment A s hoff r hr (hrk.trans_lt hlt)
    rw [show (∑ a ∈ A, ∑ b ∈ A, (2 * a - s + (2 * b - s)) ^ r) = 2 * A.card * P r from
      pair_moment_endpoints A v r hr (fun j hj hjr => by
        change P j * P (r - j) = 0; rw [hsmall j hj hjr, zero_mul])] at hw
    exact (mul_eq_zero.mp (show (2 * (A.card : ZMod p) + 2 ^ r) * P r = 0 by
      rwa [add_mul])).resolve_right hP
  have heven : Even r := by
    by_contra h
    have ho : Odd r := Nat.not_even_iff_odd.mp h
    have hmemb (a : ZMod p) (ha : a ∈ A) : s - a ∈ A :=
      (mem_filter.mp (show a ∈ reflectedPart A s by rwa [href])).2
    have hneg : (∑ a ∈ A, v (s - a) ^ r) = P r :=
      sum_bij' (fun a _ => s - a) (fun a _ => s - a) hmemb hmemb
        (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => rfl)
    have hvneg (a : ZMod p) : v (s - a) = -v a := by dsimp [v]; ring
    simp only [hvneg, ho.neg_pow, sum_neg_distrib] at hneg
    exact hP ((mul_eq_zero.mp (show (2 : ZMod p) * P r = 0 by
      change -P r = P r at hneg; linear_combination -hneg)).resolve_left h₂)
  obtain ⟨j, hj⟩ := heven
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
  refine ⟨i, by omega, ?_⟩
  have hpow : (2 : ZMod p) ^ r = 4 ^ i * 4 := by
    rw [show r = 2 * (i + 1) by omega, pow_mul, pow_succ]
    norm_num
  rw [hk, Nat.cast_mul, Nat.cast_two, hpow] at hcoeff
  have h4 : (4 : ZMod p) ≠ 0 := by
    simpa using hchar 4 (by decide) (by omega)
  have hh : (4 : ZMod p) * (4 ^ i + m) = 0 := by linear_combination hcoeff
  exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hh).resolve_left h4)

/-- If `m ≡ 1 mod 4` and `p = 2m²+1` is prime, quadratic reciprocity
excludes equality in the finite order bound. -/
theorem strict_card_of_one_mod_four (p m : ℕ) [Fact p.Prime] (hm : 1 < m)
    (hp : p = 2 * m ^ 2 + 1) (hm4 : m % 4 = 1) (A : Finset (ZMod p))
    (hA : A + A = univ) : 2 * m < A.card := by
  have hp4 : p % 4 = 3 := by simp [hp, Nat.add_mod, Nat.mul_mod, Nat.pow_mod m 2 4, hm4]
  have ho : Odd p := Nat.odd_iff.mpr (by omega)
  have hj : jacobiSym (-(m : ℤ)) p = -1 := by
    rw [jacobiSym.neg _ ho, ZMod.χ₄_nat_three_mod_four hp4,
      jacobiSym.quadratic_reciprocity_one_mod_four hm4 ho]
    have hpm : jacobiSym (p : ℤ) m = jacobiSym 1 m := by
      apply jacobiSym.mod_left'
      rw [show (p : ℤ) = 1 + (2 * (m : ℤ)) * m by exact_mod_cast (by rw [hp]; ring :
        p = 1 + 2 * m * m)]
      simp
    rw [hpm, jacobiSym.one_left, mul_one]
  have hb := order_bound A hA
  rw [ZMod.card] at hb
  by_contra! h
  have hc : A.card = 2 * m := by
    by_contra! hne
    have hsq := Nat.pow_lt_pow_left (show A.card < 2 * m by omega) (by decide : 2 ≠ 0)
    nlinarith [hp]
  obtain ⟨i, _, hi⟩ := power_of_four_necessary p m hm hp A hA hc
  apply ZMod.nonsquare_of_jacobiSym_eq_neg_one hj
  refine ⟨(2 : ZMod p) ^ i, ?_⟩
  push_cast
  rw [← hi, ← mul_pow]
  norm_num

/-- In particular, every cyclic two-basis modulo 163 has at least 19 elements. -/
theorem nineteen_le_card_mod_163 (A : Finset (ZMod 163)) (hA : A + A = univ) :
    19 ≤ A.card := by
  have : Fact (Nat.Prime 163) := ⟨by norm_num⟩
  exact strict_card_of_one_mod_four 163 9 (by decide) (by decide) (by decide) A hA

#print axioms pair_moment_endpoints
#print axioms extremal_moment
#print axioms power_of_four_necessary
#print axioms strict_card_of_one_mod_four
#print axioms nineteen_le_card_mod_163

end Green33PrimeMoments
