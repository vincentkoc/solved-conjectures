import FormalConjectures.Arxiv.«2211.10788».LucasFibonacciSumPrimes
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! Arithmetic progression divisors of the upper Lucas–Fibonacci diagonal. -/

namespace Arxiv.«2211.10788»

private abbrev QFib := QuadraticAlgebra ℕ 1 1
private abbrev w : QFib := QuadraticAlgebra.omega
private abbrev start : QFib := ⟨3, 1⟩

private lemma coeff_step (z : QFib) (n : ℕ) :
    (z * w ^ (n + 2)).im = (z * w ^ (n + 1)).im + (z * w ^ n).im := by
  have hw : w ^ 2 = w + 1 := by
    rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_add]
    simp [add_comm]
  rw [pow_add, hw, mul_add, mul_one, mul_add, pow_succ, ← mul_assoc]
  rfl

private lemma term_coeff (n : ℕ) : (start * w ^ n).im = lucasFibonacciSum n := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h0 h1 => rw [coeff_step, lucas_fibonacci_sum_recurrence, h0, h1]

private lemma fib_coeff (n : ℕ) : (w ^ n).im = Nat.fib n := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h0 h1 =>
    have h := coeff_step 1 n
    simpa [h0, h1, Nat.fib_add_two, add_comm] using h

private lemma fib_return (p d : ℕ) [NeZero p] : ∃ t > 0, p ∣ Nat.fib (d * t) := by
  let pair (n : ℕ) : ZMod p × ZMod p := (Nat.fib n, Nat.fib (n + 1))
  let step (v : ZMod p × ZMod p) := (v.2, v.1 + v.2)
  have hinj : Function.Injective step := by
    rintro ⟨a, b⟩ ⟨c, e⟩ he
    change (b, a + b) = (e, c + e) at he
    obtain ⟨rfl, h⟩ := Prod.mk.inj he
    exact Prod.ext (add_right_cancel h) rfl
  have hstep : Function.Semiconj pair Nat.succ step := fun n =>
    Prod.ext rfl (by simp [pair, step, Nat.fib_add_two])
  obtain ⟨t, ht, hfix⟩ := hinj.mem_periodicPts (pair 0)
  refine ⟨t, ht, (ZMod.natCast_eq_zero_iff ..).mp ?_⟩
  have he := (hstep.iterate_right (d * t) 0).trans (hfix.const_mul d).eq
  rw [Nat.succ_iterate] at he
  simpa [pair] using congrArg Prod.fst he

/-- First positive multiple of the index step at which the Fibonacci residue
returns to zero, counted in steps. -/
def fibonacciStepRank (p d : ℕ) [NeZero p] : ℕ := Nat.find (fib_return p d)

/-- The coefficient of the golden-ratio generator after exponentiating the
pair for the initial index of the progression. -/
def progressionPowerCoefficient (r e : ℕ) : ℕ := ((start * w ^ r) ^ e).im

private noncomputable def rootEval {K : Type*} [Field K] (a : K) (ha : a * a = 1 + a) :
    QFib →ₐ[ℕ] K :=
  QuadraticAlgebra.lift ⟨a, by simpa using ha⟩

private lemma eval_formula {K : Type*} [Field K] (a : K) (ha : a * a = 1 + a) (z : QFib) :
    rootEval a ha z = z.re + (z.im : K) * a := by
  change z.re • (1 : K) + z.im • a = _
  simp [nsmul_eq_mul]

private lemma conjugate_test {K : Type*} [Field K] {p : ℕ} [CharP K p] {a b : K}
    (ha : a * a = 1 + a) (hb : b * b = 1 + b) (hab : a ≠ b) (z : QFib) :
    p ∣ z.im ↔ rootEval a ha z = rootEval b hb z := by
  rw [← CharP.cast_eq_zero_iff K p, eval_formula, eval_formula, add_right_inj,
    mul_eq_mul_left_iff]
  simp [hab]

private lemma full_orbit {K : Type*} [Field K] {h s : K} {e : ℕ} [NeZero e]
    (hh : IsPrimitiveRoot h e) : (∃ t : ℕ, s * h ^ t = 1) ↔ s ^ e = 1 := by
  constructor
  · rintro ⟨t, ht⟩
    have he := congrArg (· ^ e) ht
    simpa [mul_pow, ← pow_mul, Nat.mul_comm t e, pow_mul h e, hh.pow_eq_one] using he
  · intro hs
    have hne : s ≠ 0 := by
      rintro rfl
      simp [NeZero.ne e] at hs
    obtain ⟨t, _, he⟩ := hh.eq_pow_of_pow_eq_one (ξ := s⁻¹) (by rw [inv_pow, hs, inv_one])
    exact ⟨t, by rw [he, mul_inv_cancel₀ hne]⟩

private lemma ordinary_test {K : Type*} [Field K] {p : ℕ} [NeZero p] [CharP K p] {a b : K}
    (ha : a * a = 1 + a) (hb : b * b = 1 + b) (hab : a ≠ b) (hb0 : b ≠ 0)
    (hstart : 3 + b ≠ 0) (r d : ℕ) :
    (∃ t : ℕ, p ∣ lucasFibonacciSum (r + d * t)) ↔
      p ∣ progressionPowerCoefficient r (fibonacciStepRank p d) := by
  let A := rootEval a ha
  let B := rootEval b hb
  let H := (a / b) ^ d
  let Y := A (start * w ^ r) / B (start * w ^ r)
  have hAw : A w = a := by simp [A, eval_formula, w]
  have hBw : B w = b := by simp [B, eval_formula, w]
  have hBs : B start = 3 + b := by simp [B, eval_formula, start]
  have hBY : B (start * w ^ r) ≠ 0 := by
    rw [map_mul, map_pow, hBs, hBw]
    exact mul_ne_zero hstart (pow_ne_zero _ hb0)
  have hF (t : ℕ) : p ∣ Nat.fib (d * t) ↔ H ^ t = 1 := by
    rw [← fib_coeff, conjugate_test ha hb hab, map_pow, map_pow]
    change A w ^ (d * t) = B w ^ (d * t) ↔ ((a / b) ^ d) ^ t = 1
    rw [hAw, hBw, ← pow_mul, div_pow, div_eq_one_iff_eq (pow_ne_zero _ hb0)]
  let e := fibonacciStepRank p d
  have he : 0 < e ∧ p ∣ Nat.fib (d * e) := Nat.find_spec (fib_return p d)
  have hh := (hF e).mp he.2
  have hord : 0 < orderOf H := orderOf_pos_iff.mpr
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨e, he.1,hh⟩)
  have heq : e = orderOf H := le_antisymm
    (Nat.find_min' (fib_return p d) ⟨hord,(hF _).mpr (pow_orderOf_eq_one H)⟩)
    (Nat.le_of_dvd he.1 (orderOf_dvd_of_pow_eq_one hh))
  let : NeZero e := ⟨he.1.ne'⟩
  have hhit (t : ℕ) : p ∣ lucasFibonacciSum (r + d * t) ↔ Y * H ^ t = 1 := by
    rw [← term_coeff, pow_add, ← mul_assoc, conjugate_test ha hb hab]
    change A ((start * w ^ r) * w ^ (d * t)) = B ((start * w ^ r) * w ^ (d * t)) ↔ _
    rw [map_mul A, map_mul B, map_pow A, map_pow B, hAw, hBw]
    dsimp only [Y, H]
    rw [← pow_mul, div_pow, div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hBY (pow_ne_zero _ hb0))]
  simp_rw [hhit]
  rw [full_orbit (show IsPrimitiveRoot H e from heq ▸ IsPrimitiveRoot.orderOf H)]
  rw [progressionPowerCoefficient, conjugate_test ha hb hab, map_pow, map_pow]
  exact div_pow (A (start * w ^ r)) (B (start * w ^ r)) e ▸ div_eq_one_iff_eq (pow_ne_zero _ hBY)

private lemma ordinary_prime {p : ℕ} (hp : p.Prime) [NeZero p] (h5 : p ≠ 5) (h11 : p ≠ 11)
    (r d : ℕ) : (∃ t : ℕ, p ∣ lucasFibonacciSum (r + d * t)) ↔
      p ∣ progressionPowerCoefficient r (fibonacciStepRank p d) := by
  let : Fact p.Prime := ⟨hp⟩
  let K := AlgebraicClosure (ZMod p)
  open Polynomial in
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root (X ^ 2 - X - 1 : K[X])
      (by have h : (X ^ 2 - X - 1 : K[X]).degree = 2 := by compute_degree!
          rw [h]; decide)
  have ha' : a * a = 1 + a := by
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one] at ha
    linear_combination ha
  let b := 1 - a
  have hb : b * b = 1 + b := by dsimp [b]; linear_combination ha'
  have hp5 : (5 : K) ≠ 0 := by
    exact_mod_cast (CharP.cast_eq_zero_iff K p 5).not.mpr
      (fun h => h5 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h))
  have hp11 : (11 : K) ≠ 0 := by
    exact_mod_cast (CharP.cast_eq_zero_iff K p 11).not.mpr
      (fun h => h11 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h))
  have hdisc : (a - b) ^ 2 = 5 := by dsimp [b]; linear_combination 4 * ha'
  have hprod : a * b = -1 := by dsimp [b]; linear_combination -ha'
  have hnorm : (3 + a) * (3 + b) = 11 := by dsimp [b]; linear_combination -ha'
  apply ordinary_test ha' hb _ _ _ r d
  · intro he
    exact hp5 (by simpa [he] using hdisc.symm)
  · intro he
    simp [he] at hprod
  · intro he
    exact hp11 (by simpa [he] using hnorm.symm)

private lemma five_dvd_term (n : ℕ) : 5 ∣ lucasFibonacciSum n ↔ n % 5 = 2 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hs (m : ℕ) : (lucasFibonacciSum (m + 5) : ZMod 5) = 3 * lucasFibonacciSum m := by
    induction m using Nat.twoStepInduction with
    | zero => decide
    | one => decide
    | more m h0 h1 =>
      rw [show m + 2 + 5 = (m + 5) + 2 by omega, lucas_fibonacci_sum_recurrence,
        lucas_fibonacci_sum_recurrence m]
      push_cast
      rw [show m + 5 + 1 = m + 1 + 5 by omega, h1, h0]
      ring
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 5
    · interval_cases n <;> decide
    have he : n - 5 + 5=n := by omega
    have hh := hs (n - 5)
    rw [he] at hh
    rw [← ZMod.natCast_eq_zero_iff, hh, mul_eq_zero,
      or_iff_right (by decide : (3 : ZMod 5) ≠ 0), ZMod.natCast_eq_zero_iff]
    exact (ih (n - 5) (by omega)).trans (by omega)

private lemma eleven_not_dvd (n : ℕ) : ¬11 ∣ lucasFibonacciSum n := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have h (m : ℕ) : (lucasFibonacciSum m : ZMod 11) = 4 ^ m := by
    induction m using Nat.twoStepInduction with
    | zero => decide
    | one => decide
    | more m h0 h1 =>
      rw [lucas_fibonacci_sum_recurrence, Nat.cast_add, h1, h0, pow_add (4 : ZMod 11) m 2, pow_succ (4 : ZMod 11) m,
        show (4 : ZMod 11) ^ 2 = 5 by decide]
      ring
  rw [← ZMod.natCast_eq_zero_iff, h]
  exact pow_ne_zero _ (by decide)

private lemma five_progression (r d : ℕ) : (∃ t : ℕ, 5 ∣ lucasFibonacciSum (r + d * t)) ↔
    (¬5 ∣ d ∨ r % 5 = 2) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  simp_rw [five_dvd_term]
  constructor
  · rintro ⟨t, ht⟩
    by_cases hd : 5 ∣ d
    · right
      simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hd] using ht
    · exact Or.inl hd
  · rintro (hd | hr)
    · have hd' : (d : ZMod 5) ≠ 0 := (ZMod.natCast_eq_zero_iff ..).not.mpr hd
      let z := (2 - (r : ZMod 5)) / d
      refine ⟨z.val, ?_⟩
      change r + d * z.val ≡ 2 [MOD 5]
      apply (ZMod.natCast_eq_natCast_iff ..).mp
      push_cast
      rw [ZMod.natCast_zmod_val]
      dsimp [z]
      field_simp
      ring
    · exact ⟨0, by simpa using hr⟩

/-- A prime divisor occurs on the prescribed index progression exactly when a
single quadratic-algebra power passes the coefficient test, with explicit
rules for the ramified prime 5 and the norm divisor 11. -/
theorem prime_dvd_lucasFibonacciSum_on_progression_iff {p : ℕ} [Fact p.Prime] (r d : ℕ) :
    (∃ t : ℕ, p ∣ lucasFibonacciSum (r + d * t)) ↔
      if p = 5 then ¬5 ∣ d ∨ r % 5 = 2
      else p ≠ 11 ∧ p ∣ progressionPowerCoefficient r (fibonacciStepRank p d) := by
  split_ifs with hp
  · subst p
    exact five_progression r d
  by_cases he : p = 11
  · subst p
    simp [eleven_not_dvd]
  · simpa [he] using ordinary_prime (Fact.out : p.Prime) hp he r d

lemma fibonacciStepRank_dvd_iff (m d t : ℕ) [NeZero m] :
    fibonacciStepRank m d ∣ t ↔ m ∣ Nat.fib (d * t) := by
  let e := fibonacciStepRank m d
  have he : 0 < e ∧ m ∣ Nat.fib (d * e) := Nat.find_spec (fib_return m d)
  constructor
  · intro h
    exact he.2.trans (Nat.fib_dvd _ _ (Nat.mul_dvd_mul_left d h))
  · intro ht
    have hg : m ∣ Nat.fib (d * e.gcd t) := by
      rw [← Nat.gcd_mul_left, Nat.fib_gcd]
      exact Nat.dvd_gcd he.2 ht
    have hle : e ≤ e.gcd t := Nat.find_min' (fib_return m d)
      ⟨Nat.gcd_pos_of_pos_left t he.1, hg⟩
    have heq : e = e.gcd t := le_antisymm hle (Nat.le_of_dvd he.1 (Nat.gcd_dvd_left ..))
    change e ∣ t
    calc e ∣ e.gcd t := dvd_of_eq heq
         _ ∣ t := Nat.gcd_dvd_right e t

private lemma coefficients_coprime (s : ℕ) :
    Nat.Coprime (start * w ^ s).im (start * w ^ s).re := by
  induction s with
  | zero => decide
  | succ s ih =>
    rw [pow_succ, ← mul_assoc]
    simpa [w, Nat.coprime_add_self_left] using ih.symm

/-- Once any modulus divides a term, its subsequent occurrences on a given
index step are exactly the multiples of the Fibonacci return rank. -/
theorem lucasFibonacciSum_dvd_after_hit_iff {m s : ℕ} [NeZero m]
    (hs : m ∣ lucasFibonacciSum s) (d t : ℕ) :
    m ∣ lucasFibonacciSum (s + d * t) ↔ fibonacciStepRank m d ∣ t := by
  let z := start * w ^ s
  have hy : m ∣ z.im := term_coeff s ▸ hs
  have hx : m.Coprime z.re := (coefficients_coprime s).of_dvd_left hy
  rw [fibonacciStepRank_dvd_iff, ← term_coeff, pow_add, ← mul_assoc]
  change m ∣ (z * w ^ (d * t)).im ↔ _
  have hother : m ∣ z.im * (w ^ (d * t)).re + z.im * (w ^ (d * t)).im :=
    dvd_add (dvd_mul_of_dvd_left hy _) (dvd_mul_of_dvd_left hy _)
  rw [QuadraticAlgebra.im_mul, one_mul, add_assoc, Nat.dvd_add_left hother, hx.dvd_mul_left,
    fib_coeff]

example : fibonacciStepRank 47 1 = 16 ∧ progressionPowerCoefficient 0 16 % 47 = 8 := by
  constructor
  · apply (Nat.find_eq_iff (fib_return 47 1)).mpr
    refine ⟨by decide, ?_⟩
    intro m hm
    interval_cases m <;> decide
  · decide

#print axioms prime_dvd_lucasFibonacciSum_on_progression_iff
#print axioms lucasFibonacciSum_dvd_after_hit_iff

end Arxiv.«2211.10788»
