import FormalConjectures.Arxiv.«2211.10788».LucasFibonacciSumPrimes
import Mathlib.NumberTheory.AlmostPrime

/-! Ching et al., arXiv:2211.10788, ask when both Fₙ + Lₙ₋₁ and Fₙ + Lₙ₊₁ are prime.
We index n = m + 2 so both neighboring Lucas numbers have positive indices. -/

namespace Arxiv.«2211.10788»

/-- The lower neighbor at index m + 2, since Lₘ₊₁ = Fₘ + Fₘ₊₂. -/
def lowerNeighborAtAddTwo (m : ℕ) : ℕ := 2 * Nat.fib (m + 2) + Nat.fib m

theorem fib_pair_norm (m : ℕ) :
    (Nat.fib (m + 1) : ℤ) ^ 2 - Nat.fib m * Nat.fib (m + 1) - (Nat.fib m : ℤ) ^ 2 =
      (-1) ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [show m.succ + 1 = m + 2 by rfl, Nat.fib_add_two, Nat.cast_add, pow_succ]
    linear_combination -ih

/-- The two neighboring sums factor an explicit shifted Fibonacci square. -/
theorem lucasFibonacciSum_mul_lowerNeighbor (m : ℕ) :
    (lucasFibonacciSum (m + 2) : ℤ) * lowerNeighborAtAddTwo m =
      11 * (Nat.fib (m + 2) : ℤ) ^ 2 - (-1) ^ m := by
  simp only [lucasFibonacciSum, lowerNeighborAtAddTwo, Nat.fib_add_two, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat]
  linear_combination -(fib_pair_norm m)

private theorem fib_period_42 (m : ℕ) : Nat.fib (m + 48) ≡ Nat.fib m [MOD 42] := by
  induction m using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more m h₀ h₁ =>
    rw [show m + 2 + 48 = (m + 48) + 2 by omega,
      Nat.fib_add_two (n := m + 48), Nat.fib_add_two (n := m)]
    exact h₀.add h₁

/-- The product survives division by 2, 3 and 7 in exactly three classes modulo 24. -/
theorem neighboring_product_coprime_42_iff (m : ℕ) :
    (lucasFibonacciSum (m + 2) * lowerNeighborAtAddTwo m).Coprime 42 ↔
      (m + 2) % 24 ∈ ({0, 6, 18} : Finset ℕ) := by
  let g (j : ℕ) := (lucasFibonacciSum (j + 2) * lowerNeighborAtAddTwo j).gcd 42
  have per : Function.Periodic g 48 := by
    intro j
    apply Nat.ModEq.gcd_eq
    unfold lucasFibonacciSum lowerNeighborAtAddTwo
    rw [show j + 48 + 2 = j + 2 + 48 by omega,
      show j + 2 + 48 + 2 = j + 2 + 2 + 48 by omega]
    exact (((fib_period_42 (j + 2)).mul_left 2).add (fib_period_42 (j + 2 + 2))).mul
      (((fib_period_42 (j + 2)).mul_left 2).add (fib_period_42 j))
  have table : ∀ j : Fin 48, g j = 1 ↔ (j.val + 2) % 24 ∈ ({0, 6, 18} : Finset ℕ) := by decide
  have he := per.nat_mul (m / 48) (m % 48)
  change g (m % 48 + (m / 48) * 48) = g (m % 48) at he
  rw [Nat.mul_comm (m / 48), Nat.mod_add_div] at he
  change g m = 1 ↔ _
  rw [he]
  simpa only [show (m % 48 + 2) % 24 = (m + 2) % 24 by omega] using
    table ⟨m % 48, Nat.mod_lt _ (by decide)⟩

/-- Apart from the index 2 pair, the neighboring prime-pair question reduces to
semiprimality of 11 Fₙ² − 1 in three residue classes. -/
theorem neighboring_primes_iff_semiprime (m : ℕ) :
    ((lucasFibonacciSum (m + 2)).Prime ∧ (lowerNeighborAtAddTwo m).Prime) ↔
      m = 0 ∨ ((m + 2) % 24 ∈ ({0, 6, 18} : Finset ℕ) ∧
        Nat.IsAlmostPrime 2 (11 * Nat.fib (m + 2) ^ 2 - 1)) := by
  rcases lt_or_ge m 6 with hsmall | hm
  · interval_cases m <;> try decide
    exact iff_of_true (by decide) (Or.inr ⟨by decide,
      (by decide : Nat.Prime 37).mul_isAlmostPrime_two (by decide : Nat.Prime 19)⟩)
  have hf : 21 ≤ Nat.fib (m + 2) := Nat.fib_mono (by omega : 8 ≤ m + 2)
  have ht : 8 ≤ Nat.fib m := Nat.fib_mono hm
  have hu : 55 ≤ Nat.fib (m + 2 + 2) := Nat.fib_mono (by omega : 10 ≤ m + 2 + 2)
  have hplus : 42 < lucasFibonacciSum (m + 2) := by unfold lucasFibonacciSum; omega
  have hminus : 42 < lowerNeighborAtAddTwo m := by unfold lowerNeighborAtAddTwo; omega
  have prod (h : (m + 2) % 24 ∈ ({0, 6, 18} : Finset ℕ)) :
      lucasFibonacciSum (m + 2) * lowerNeighborAtAddTwo m = 11 * Nat.fib (m + 2) ^ 2 - 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    have heven : Even m := by rw [Nat.even_iff]; omega
    have hnat : 1 ≤ 11 * Nat.fib (m + 2) ^ 2 := by nlinarith
    have he := lucasFibonacciSum_mul_lowerNeighbor m
    rw [heven.neg_one_pow] at he
    zify [hnat]
    exact he
  constructor
  · rintro ⟨hp, hq⟩
    have hr := (neighboring_product_coprime_42_iff m).mp (Nat.coprime_mul_iff_left.mpr
      ⟨hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hplus),
        hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hminus)⟩)
    exact Or.inr ⟨hr, prod hr ▸ hp.mul_isAlmostPrime_two hq⟩
  · rintro (h | ⟨hr, h⟩)
    · omega
    · rw [← prod hr] at h
      have hc := h.2
      rw [ArithmeticFunction.cardFactors_mul (by omega) (by omega)] at hc
      have ha := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr
        (show 1 < lucasFibonacciSum (m + 2) by omega)
      have hb := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr
        (show 1 < lowerNeighborAtAddTwo m by omega)
      exact ⟨ArithmeticFunction.cardFactors_eq_one_iff_prime.mp (by omega),
        ArithmeticFunction.cardFactors_eq_one_iff_prime.mp (by omega)⟩

#print axioms fib_pair_norm
#print axioms lucasFibonacciSum_mul_lowerNeighbor
#print axioms neighboring_product_coprime_42_iff
#print axioms neighboring_primes_iff_semiprime

end Arxiv.«2211.10788»
