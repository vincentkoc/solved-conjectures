import OMAStatements.S_oeis_a262779
import Mathlib

-- Problem: A262779: Binary representation of the n-th iteration of the "Rule 175" elementary cellular automaton starting with a single ON (black) cell
-- Upstream: formal-conjectures statements/oeis-a262779.lean:0 (declaration OMA.S_oeis_a262779.main)
-- Credit: @vincentkoc (the owner of the agent is credited as the solver)
-- Proof: Rule 175 sends (l, c, r) to (!l || r). From a single ON cell, after t ≥ 1 steps every
-- cell is ON except the one at position 2 - t, so 9 * a(n) = 10^(2n+1) - 1 - 9 * 10^(2n-2)
-- for n ≥ 1. The recurrence and the generating function follow from this closed form.

namespace OMA.A262779Proof

open OMA.S_oeis_a262779 PowerSeries

lemma ruleOut_175 (l c r : Bool) : ruleOut 175 l c r = (!l || r) := by
  cases l <;> cases c <;> cases r <;> decide

lemma cell_175 (t : ℕ) (ht : 1 ≤ t) (i : ℤ) : cell 175 t i = decide (i ≠ 2 - t) := by
  induction t generalizing i with
  | zero => omega
  | succ t ih =>
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · simp only [cell, ruleOut_175]
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        decide_eq_true_eq]
      push_cast
      omega
    · simp only [cell, ruleOut_175]
      rw [ih htpos, ih htpos, Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        decide_eq_true_eq]
      push_cast
      omega

lemma geom (m : ℕ) : 9 * ∑ j ∈ Finset.range m, (10 : ℤ) ^ (m - 1 - j) = 10 ^ m - 1 := by
  rw [Finset.sum_range_reflect (fun j => (10 : ℤ) ^ j) m]
  have := geom_sum_mul (10 : ℤ) m
  linarith

lemma nine_mul_a (n : ℕ) (hn : 1 ≤ n) :
    9 * a n = 10 ^ (2 * n + 1) - 1 - 9 * 10 ^ (2 * n - 2) := by
  have hsum : a n = ∑ j ∈ Finset.range (2 * n + 1), (10 : ℤ) ^ (2 * n + 1 - 1 - j)
      - 10 ^ (2 * n - 2) := by
    unfold a
    have h1 : ∀ j ∈ Finset.range (2 * n + 1),
        (if cell 175 n ((j : ℤ) - n) then (10 : ℤ) ^ (2 * n - j) else 0) =
          (10 : ℤ) ^ (2 * n + 1 - 1 - j) - if j = 2 then (10 : ℤ) ^ (2 * n - 2) else 0 := by
      intro j _
      rw [cell_175 n hn]
      have e : 2 * n + 1 - 1 - j = 2 * n - j := by omega
      rw [e]
      by_cases hj : j = 2
      · subst hj; simp
      · have : ((j : ℤ) - n ≠ 2 - n) := by omega
        simp [this, hj]
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_ite_eq']
    have : 2 ∈ Finset.range (2 * n + 1) := Finset.mem_range.mpr (by omega)
    simp [this]
  rw [hsum, mul_sub, geom]

theorem rec (m : ℕ) : a (m + 3) = 101 * a (m + 2) - 100 * a (m + 1) := by
  have h3 := nine_mul_a (m + 3) (by omega)
  have h2 := nine_mul_a (m + 2) (by omega)
  have h1 := nine_mul_a (m + 1) (by omega)
  have e3 : 2 * (m + 3) - 2 = 2 * m + 4 := by omega
  have e2 : 2 * (m + 2) - 2 = 2 * m + 2 := by omega
  have e1 : 2 * (m + 1) - 2 = 2 * m := by omega
  rw [e3] at h3; rw [e2] at h2; rw [e1] at h1
  have : 9 * (a (m + 3) - (101 * a (m + 2) - 100 * a (m + 1))) = 0 := by
    rw [mul_sub, mul_sub, mul_left_comm 9 101, mul_left_comm 9 100, h3, h2, h1]
    ring
  omega

lemma a_zero : a 0 = 1 := by
  simp [a, cell]

lemma a_one : a 1 = 110 := by
  have := nine_mul_a 1 le_rfl
  norm_num at this
  omega

lemma a_two : a 2 = 11011 := by
  have := nine_mul_a 2 (by norm_num)
  norm_num at this
  omega

end OMA.A262779Proof

open OMA.S_oeis_a262779 OMA.A262779Proof PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a262779.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    simpa using rec m
  · have hX : (PowerSeries.mk fun n => (a n : ℚ)) * ((1 - X) * (1 - 100 * X)) =
        PowerSeries.mk (fun n => (a n : ℚ))
          - C (101 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
          + C (100 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2) := by
      simp only [map_ofNat]
      ring
    rw [hX, show (1 + 9 * X + X ^ 2 : PowerSeries ℚ) = 1 + C (9 : ℚ) * X ^ 1 + X ^ 2 by
      simp only [map_ofNat]; ring]
    ext k
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases k with _ | _ | _ | m
    · simp [a_zero]
    · simp [a_zero, a_one, coeff_X_pow]
      norm_num
    · simp [a_zero, a_one, a_two, coeff_X_pow]
      norm_num
    · have h := rec m
      have e1 : m + 3 - 1 = m + 2 := by omega
      have e2 : m + 3 - 2 = m + 1 := by omega
      simp only [e1, e2, show 1 ≤ m + 3 by omega, show 2 ≤ m + 3 by omega, if_true]
      have hq : ((a (m + 3) : ℤ) : ℚ) = 101 * (a (m + 2) : ℚ) - 100 * (a (m + 1) : ℚ) := by
        exact_mod_cast h
      rw [hq]
      simp [coeff_X_pow, coeff_one]
