import ThetaDiagonalModEight

/-! A characteristic-p power-moment expansion of the canonical theta sum. -/

namespace Arxiv.«2501.03234».ThetaTangent

open Finset
open ThetaDiagonal (U rep sign oddReps)

variable {p : ℕ} [Fact p.Prime]

/-- Integral coefficients of the exponential generating series tanh(t) − 1. -/
def tangentCoeff : ℕ → ℤ
  | 0 => -1
  | n + 1 => - ∑ i : Fin (n+1),
      ((n+1).choose i : ℤ) * 2^(n-i.val) * tangentCoeff i.val
termination_by n => n
decreasing_by exact i.isLt

/-- The finite convolution from the characteristic-p interpolation formula. -/
def tangentConvolution (n : ℕ) : ℤ :=
  ∑ i ∈ Ico 1 n, 2^(n-i) * (tangentCoeff i)^2 * tangentCoeff (n-i)

private def moment (p : ℕ) [Fact p.Prime] (i : ℕ) : ZMod p :=
  ∑ a ∈ oddReps p, (a : ZMod p)^i

private lemma kernel (u c : U p) :
    ∑ i ∈ range (p-1), ((u : ZMod p) / c)^i =
      if u = c then -1 else 0 := by
  split_ifs with h
  · subst c
    simp only [div_self u.ne_zero, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
    rw [Nat.cast_sub (Fact.out : p.Prime).one_le]
    simp
  · have hne : (u : ZMod p) / c ≠ 1 :=
      fun hh => h (Units.ext ((div_eq_one_iff_eq c.ne_zero).mp hh))
    have hn := ZMod.pow_card_sub_one_eq_one (div_ne_zero u.ne_zero c.ne_zero)
    exact (mul_eq_zero.mp (show (∑ i ∈ range (p-1), ((u : ZMod p)/c)^i) *
      ((u : ZMod p)/c - 1) = 0 by rw [geom_sum_mul, hn, sub_self])).resolve_right
        (sub_ne_zero.mpr hne)

private lemma inverse_power (c : U p) {i : ℕ} (hi : i ≤ p-1) :
    ((c : ZMod p) ^ i)⁻¹ = (c : ZMod p)^(p-1-i) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_add, Nat.add_sub_of_le hi]
  exact ZMod.pow_card_sub_one_eq_one c.ne_zero

private lemma kernel_expand (u c : U p) :
    ∑ i ∈ range (p-1), (u : ZMod p)^i * (c : ZMod p)^(p-1-i) =
      if u = c then -1 else 0 := by
  rw [← kernel]
  apply sum_congr rfl
  intro i hi
  rw [div_pow, div_eq_mul_inv, inverse_power c (mem_range.mp hi).le]

private lemma odd_sign_interp (hp : p % 2 = 1) (u : U p) :
    (sign u : ZMod p) = -2 * ∑ i ∈ Ico 1 (p-1), (u : ZMod p)^i * moment p (p-1-i) := by
  have h : (∑ i ∈ range (p-1), (u : ZMod p)^i * moment p (p-1-i)) =
      (if u ∈ oddReps p then -1 else 0) := by
    simp only [moment, mul_sum]
    rw [sum_comm]
    simp [kernel_expand]
  have hprime := (Fact.out : p.Prime).two_le
  have hrest := sum_Ico_consecutive (f := fun i => (u : ZMod p)^i * moment p (p-1-i))
    (show 0 ≤ 1 by decide) (show 1 ≤ p-1 by omega)
  rw [Nat.Ico_zero_eq_range, Nat.Ico_zero_eq_range, sum_range_one] at hrest
  have hfirst : moment p (p-1) = (p/2 : ℕ) := by
    simp [moment, ZMod.pow_card_sub_one_eq_one, ThetaDiagonal.card_oddReps hp]
  simp only [pow_zero, one_mul, Nat.sub_zero, hfirst] at hrest
  have hm : 2 * ((p/2 : ℕ) : ZMod p) = -1 := by
    have hh : 2*(p/2)+1=p := by omega
    have he := congrArg (fun n : ℕ => (n : ZMod p)) hh
    push_cast at he; rw [ZMod.natCast_self] at he; linear_combination he
  by_cases hu : u ∈ oddReps p
  · rw [if_pos hu] at h
    simp only [sign, if_pos (mem_filter.mp hu).2, Int.cast_one]
    linear_combination 2 * hrest + 2 * h - hm
  · rw [if_neg hu] at h
    have he : rep u % 2 ≠ 1 := by intro he; exact hu (mem_filter.mpr ⟨mem_univ _, he⟩)
    simp only [sign, if_neg he, Int.cast_neg, Int.cast_one]
    linear_combination 2 * hrest + 2 * h - hm

/-- Power-moment expansion of S(p) in its own prime field. -/
private lemma S_eq_moments (hp : p % 2 = 1) :
    (S p : ZMod p) = -4 * ∑ i ∈ Ico 1 (p-1), moment p i ^ 2 * moment p (p-1-i) := by
  rw [ThetaDiagonal.S_eq_odd_square hp]
  push_cast
  simp_rw [odd_sign_interp hp]
  simp only [← mul_sum, Units.val_mul, mul_pow]
  rw [show (∑ a ∈ oddReps p, ∑ b ∈ oddReps p, ∑ i ∈ Ico 1 (p-1),
      (b : ZMod p)^i * (a : ZMod p)^i * moment p (p-1-i)) =
      ∑ i ∈ Ico 1 (p-1), moment p i ^ 2 * moment p (p-1-i) by
    calc
      _ = ∑ a ∈ oddReps p, ∑ i ∈ Ico 1 (p-1),
          (moment p i * (a : ZMod p)^i * moment p (p-1-i)) := by
            apply sum_congr rfl; intro a _; rw [sum_comm]
            simp only [← sum_mul, moment]
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl; intro i _
        rw [← sum_mul, ← mul_sum, sq]
        rfl]
  ring

private lemma split_units (hp : p % 2 = 1) (f : ZMod p → ZMod p) :
    (∑ a ∈ oddReps p, f a) + ∑ a ∈ oddReps p, f ((a : ZMod p)+1) =
      ∑ u : U p, f u := by
  classical
  rw [← sum_filter_add_sum_filter_not univ (fun a : U p => rep a % 2 = 1) (fun a => f a)]
  congr 1
  have hval (a : U p) (ha : a ∈ oddReps p) : rep a + 1 < p := by
    have := (mem_filter.mp ha).2
    have : rep a < p := ZMod.val_lt _
    omega
  have hn (a : U p) (ha : a ∈ oddReps p) : ((rep a+1 : ℕ) : ZMod p) ≠ 0 := by
    intro h
    have := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (hval a ha)] at this
    simp at this
  apply sum_bij (fun a ha => Units.mk0 ((rep a + 1 : ℕ) : ZMod p) (hn a ha))
  · intro a ha
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    change ¬ (((rep a + 1 : ℕ) : ZMod p).val % 2 = 1)
    rw [ZMod.val_natCast_of_lt (hval a ha)]
    have := (mem_filter.mp ha).2; omega
  · intro a ha b hb h
    have he := congrArg rep h
    change ((rep a+1 : ℕ) : ZMod p).val = ((rep b+1 : ℕ) : ZMod p).val at he
    rw [ZMod.val_natCast_of_lt (hval a ha), ZMod.val_natCast_of_lt (hval b hb)] at he
    exact Units.ext (ZMod.val_injective p (Nat.add_right_cancel he))
  · intro b hb
    have he := (mem_filter.mp hb).2
    have hlt : rep b < p := ZMod.val_lt _
    have hpos : rep b ≠ 0 := fun h => b.ne_zero ((ZMod.val_eq_zero _).mp h)
    have hpred : rep b-1 < p := by omega
    let a : U p := Units.mk0 ((rep b-1 : ℕ) : ZMod p) (by
      intro h; have hh := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt hpred] at hh
      rw [ZMod.val_zero] at hh
      omega)
    have ha : rep a = rep b - 1 := ZMod.val_natCast_of_lt hpred
    refine ⟨a, mem_filter.mpr ⟨mem_univ _, by rw [ha]; omega⟩, Units.ext ?_⟩
    change ((rep a+1 : ℕ) : ZMod p) = (b : ZMod p)
    rw [ha, Nat.sub_add_cancel (by omega)]; exact ZMod.natCast_zmod_val _
  · intro a _
    change f ((a : ZMod p)+1) = f ((rep a+1 : ℕ) : ZMod p)
    simp [rep]

private lemma moment_step (hp : p % 2 = 1) {n : ℕ} (hn : n+1 < p-1) :
    2 * moment p (n+1) + ∑ i ∈ range (n+1), ((n+1).choose i : ZMod p) * moment p i = 0 := by
  have h := split_units hp (fun a => a^(n+1))
  rw [FiniteField.sum_pow_units, ZMod.card, if_neg (Nat.not_dvd_of_pos_of_lt (by omega) hn)] at h
  have hx (a : U p) : ((a : ZMod p)+1)^(n+1) =
      (∑ i ∈ range (n+1), (a : ZMod p)^i * ((n+1).choose i : ZMod p)) + (a : ZMod p)^(n+1) := by
    rw [add_pow, sum_range_succ]; simp
  simp_rw [hx] at h
  rw [sum_add_distrib, sum_comm] at h
  simp only [← sum_mul] at h
  change moment p (n+1) + ((∑ i ∈ range (n+1), moment p i * ((n+1).choose i : ZMod p)) +
    moment p (n+1)) = 0 at h
  simp_rw [mul_comm (((n+1).choose _ : ℕ) : ZMod p) _]
  linear_combination h

private lemma scaled_moment (hp : p % 2 = 1) {k : ℕ} (hk : k < p-1) :
    2^(k+1) * moment p k = (tangentCoeff k : ZMod p) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      simp only [zero_add, pow_one, moment, pow_zero, sum_const, nsmul_eq_mul, mul_one,
        ThetaDiagonal.card_oddReps hp, tangentCoeff, Int.cast_neg, Int.cast_one]
      have hh : 2*(p/2)+1=p := by omega
      have he := congrArg (fun n : ℕ => (n : ZMod p)) hh
      push_cast at he; rw [ZMod.natCast_self] at he
      linear_combination he
    | succ n =>
      rw [tangentCoeff]
      push_cast
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((n+1).choose i : ZMod p) * 2^(n-i) * (tangentCoeff i : ZMod p))]
      have hs := moment_step hp hk
      have ht (i : ℕ) (hi : i ∈ range (n+1)) :
          ((n+1).choose i : ZMod p) * 2^(n-i) * (tangentCoeff i : ZMod p) =
            (2 : ZMod p)^(n+1) * (((n+1).choose i : ZMod p) * moment p i) := by
        have hi' := mem_range.mp hi
        rw [← ih i hi' (by omega)]
        have he : (2 : ZMod p)^(n-i) * 2^(i+1) = 2^(n+1) := by
          rw [← pow_add]; congr 1; omega
        linear_combination ((n+1).choose i : ZMod p) * moment p i * he
      rw [sum_congr rfl ht, ← mul_sum, pow_succ]
      linear_combination (2 : ZMod p)^(n+1) * hs

private lemma two_ne_zero (hp : p % 2 = 1) : (2 : ZMod p) ≠ 0 := by
  have h := (Fact.out : p.Prime).two_le
  have hlt : 2 < p := by omega
  intro he
  have hval := congrArg ZMod.val he
  change ((2 : ℕ) : ZMod p).val = (0 : ZMod p).val at hval
  rw [ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at hval
  contradiction

private lemma convolution_cast (hp : p % 2 = 1) :
    (tangentConvolution (p-1) : ZMod p) =
      8 * ∑ i ∈ Ico 1 (p-1), moment p i ^ 2 * moment p (p-1-i) := by
  unfold tangentConvolution
  push_cast
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  obtain ⟨hi1, hi2⟩ := mem_Ico.mp hi
  rw [← scaled_moment hp hi2, ← scaled_moment hp (show p-1-i < p-1 by omega), mul_pow]
  have hpow : (2 : ZMod p)^(p-1-i) * (2^(i+1))^2 * 2^(p-1-i+1) = 8 := by
    rw [← pow_mul, ← pow_add, ← pow_add,
      show p-1-i+(i+1)*2+(p-1-i+1) = (p-1)*2+3 by omega, pow_add, pow_mul,
      ZMod.pow_card_sub_one_eq_one (two_ne_zero hp)]
    norm_num
  linear_combination (moment p i)^2 * moment p (p-1-i) * hpow

/-- A single integral sequence determines the canonical theta sum modulo every odd prime. -/
theorem S_mod_prime_tangent (p : ℕ) (hprime : p.Prime) (hp : p % 2 = 1) :
    2 * S p ≡ -tangentConvolution (p-1) [ZMOD (p : ℤ)] := by
  let : Fact p.Prime := ⟨hprime⟩
  apply (ZMod.intCast_eq_intCast_iff _ _ p).mp
  push_cast
  rw [S_eq_moments hp, convolution_cast hp]
  ring

/-- Divisibility by the argument prime can be tested on the integral convolution. -/
theorem prime_dvd_S_iff (p : ℕ) (hprime : p.Prime) (hp : p % 2 = 1) :
    (p : ℤ) ∣ S p ↔ (p : ℤ) ∣ tangentConvolution (p-1) := by
  let : Fact p.Prime := ⟨hprime⟩
  have he := (ZMod.intCast_eq_intCast_iff _ _ p).mpr (S_mod_prime_tangent p hprime hp)
  push_cast at he
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro h; rw [h, mul_zero] at he; exact neg_eq_zero.mp he.symm
  · intro h; rw [h, neg_zero] at he; exact (mul_eq_zero.mp he).resolve_left (two_ne_zero hp)

/-- A nonzero convolution residue rules out a zero of the integer theta sum. -/
theorem S_ne_zero_of_tangent (p : ℕ) (hprime : p.Prime) (hp : p % 2 = 1)
    (h : ¬ (p : ℤ) ∣ tangentConvolution (p-1)) : S p ≠ 0 := by
  intro hz
  apply h
  exact (prime_dvd_S_iff p hprime hp).mp (hz ▸ dvd_zero _)

end Arxiv.«2501.03234».ThetaTangent

#print axioms Arxiv.«2501.03234».ThetaTangent.S_mod_prime_tangent
#print axioms Arxiv.«2501.03234».ThetaTangent.prime_dvd_S_iff
#print axioms Arxiv.«2501.03234».ThetaTangent.S_ne_zero_of_tangent
