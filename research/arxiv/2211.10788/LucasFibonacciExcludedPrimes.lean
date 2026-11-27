import FormalConjectures.Arxiv.«2211.10788».LucasFibonacciSumPrimes
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! Five residue classes of primes divide no term of the Lucas–Fibonacci sum
sequence of Ching et al. This sequence starts one term into the Lagarias sequence. -/

namespace Arxiv.«2211.10788»

private theorem cassini (p n : ℕ) :
    (-1 : ZMod p) ^ n * ((lucasFibonacciSum (n + 1) : ZMod p) ^ 2 -
      lucasFibonacciSum n * lucasFibonacciSum (n + 1) - (lucasFibonacciSum n : ZMod p) ^ 2) = 11 := by
  induction n with
  | zero => norm_num [lucas_fibonacci_sum_zero, lucas_fibonacci_sum_one]
  | succ n ih =>
    rw [show n.succ + 1 = n + 2 by rfl, lucas_fibonacci_sum_recurrence, Nat.cast_add, pow_succ]
    linear_combination ih

/-- A prime congruent to one modulo four dividing any term is a square modulo eleven. -/
theorem isSquare_mod_eleven_of_prime_dvd_lucasFibonacciSum {p n : ℕ} (hp : p.Prime)
    (hp4 : p % 4 = 1) (hd : p ∣ lucasFibonacciSum n) : IsSquare (p : ZMod 11) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hz := (ZMod.natCast_eq_zero_iff ..).mpr hd
  have h := cassini p n
  simp only [hz, zero_mul, sub_zero, zero_pow (by decide : 2 ≠ 0)] at h
  have hs : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
  apply (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one hp4 (by decide : 11 ≠ 2)).mp
  rw [Nat.cast_ofNat, ← h]
  exact (hs.pow n).mul (IsSquare.sq _)

/-- Each listed residue class consists, among primes, entirely of nondivisors. -/
theorem not_dvd_lucasFibonacciSum_of_mod_44 {p : ℕ} (hp : p.Prime)
    (hr : p % 44 ∈ ({13, 17, 21, 29, 41} : Finset ℕ)) (n : ℕ) : ¬ p ∣ lucasFibonacciSum n := by
  intro hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  have h4 : p % 4 = 1 := by omega
  have hs := isSquare_mod_eleven_of_prime_dvd_lucasFibonacciSum hp h4 hd
  have hcast : (p : ZMod 11) = ((p % 44 : ℕ) : ZMod 11) :=
    (ZMod.natCast_eq_natCast_iff ..).mpr ((Nat.mod_modEq p 44).symm.of_dvd (by decide))
  rw [hcast] at hs
  rcases hr with h | h | h | h | h <;> rw [h] at hs <;> revert hs <;> decide

/-- In each of the five classes there are infinitely many primes that divide no term. -/
theorem infinite_nondivisors_lucasFibonacciSum_in_class (r : ℕ)
    (hr : r ∈ ({13, 17, 21, 29, 41} : Finset ℕ)) :
    {p : ℕ | p.Prime ∧ p % 44 = r ∧ ∀ n, ¬p ∣ lucasFibonacciSum n}.Infinite := by
  have hr' : r.Coprime 44 ∧ r < 44 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  apply (Nat.infinite_setOfPred_prime_and_modEq (by decide : 44 ≠ 0) hr'.1).mono
  rintro p ⟨hp, hc⟩
  have he : p % 44 = r := by simpa only [Nat.ModEq, Nat.mod_eq_of_lt hr'.2] using hc
  exact ⟨hp, he, not_dvd_lucasFibonacciSum_of_mod_44 hp (he ▸ hr)⟩

#print axioms isSquare_mod_eleven_of_prime_dvd_lucasFibonacciSum
#print axioms not_dvd_lucasFibonacciSum_of_mod_44
#print axioms infinite_nondivisors_lucasFibonacciSum_in_class

end Arxiv.«2211.10788»
