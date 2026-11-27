import FormalConjectures.Arxiv.«2211.10788».LucasFibonacciSumPrimes

/-! A Pell equation and a residue condition select exactly the upper Lucas–Fibonacci
diagonal in the prime-values question of Ching et al. -/

namespace Arxiv.«2211.10788»

private def normEleven (a b : ℕ) : Prop :=
  b ^ 2 = a * b + a ^ 2 + 11 ∨ b ^ 2 + 11 = a * b + a ^ 2

private theorem norm_step (a b : ℕ) : normEleven a b ↔ normEleven b (a + b) := by
  unfold normEleven
  constructor <;> rintro (h | h)
  · right; nlinarith only [h]
  · left; nlinarith only [h]
  · right; nlinarith only [h]
  · left; nlinarith only [h]

private theorem pair_properties (n : ℕ) :
    0 < lucasFibonacciSum n ∧ lucasFibonacciSum n < lucasFibonacciSum (n + 1) ∧
    lucasFibonacciSum (n + 1) ≡ 4 * lucasFibonacciSum n [MOD 11] ∧
    normEleven (lucasFibonacciSum n) (lucasFibonacciSum (n + 1)) := by
  induction n with
  | zero => unfold normEleven; decide
  | succ n ih =>
    obtain ⟨hpos, hlt, hmod, hnorm⟩ := ih
    rw [show n.succ + 1 = n + 2 by rfl, lucas_fibonacci_sum_recurrence]
    refine ⟨hpos.trans hlt, by omega, ?_, ?_⟩
    · change (_ + _) % 11 = (4 * _) % 11
      change _ % 11 = _ % 11 at hmod
      omega
    · simpa only [add_comm (lucasFibonacciSum n)] using (norm_step _ _).mp hnorm

private theorem base_pair {a b : ℕ} (hab : 2 * a ≤ b) (hn : normEleven a b)
    (hm : b ≡ 4 * a [MOD 11]) : a = 1 ∧ b = 4 := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hab
  have heq : a ^ 2 + 3 * a * e + e ^ 2 = 11 := by
    rcases hn with h | h
    · nlinarith only [h]
    · nlinarith [Nat.zero_le (a * e)]
  have bound (v : ℕ) (hv : v ^ 2 ≤ 11) : v ≤ 3 := by
    by_contra! h
    nlinarith only [hv, Nat.mul_self_le_mul_self (show 4 ≤ v by omega)]
  have ha := bound a (by omega)
  have he := bound e (by omega)
  interval_cases a <;> interval_cases e <;> norm_num [Nat.ModEq] at *

/-- Descend a positive increasing pair. The norm permits two initial pairs,
(1,4) and (2,5); the congruence selects (1,4). -/
private theorem pair_is_consecutive {a b : ℕ} (hab : a < b) (hn : normEleven a b)
    (hm : b ≡ 4 * a [MOD 11]) :
    ∃ n, lucasFibonacciSum n = a ∧ lucasFibonacciSum (n + 1) = b := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases hbase : 2 * a ≤ b
    · obtain ⟨rfl, rfl⟩ := base_pair hbase hn hm
      exact ⟨0, lucas_fibonacci_sum_zero, lucas_fibonacci_sum_one⟩
    · let c := b - a
      have hc : c + a = b := Nat.sub_add_cancel hab.le
      have hlt : c < a := by omega
      have hn' : normEleven c a := (norm_step c a).mpr (hc ▸ hn)
      have hm' : a ≡ 4 * c [MOD 11] := by
        change _ % 11 = _ % 11 at hm ⊢
        omega
      obtain ⟨n, hfirst, hnext⟩ := ih c hlt hlt hn' hm'
      refine ⟨n + 1, hnext, ?_⟩
      rw [show n + 1 + 1 = n + 2 by rfl, lucas_fibonacci_sum_recurrence, hfirst, hnext]
      omega

private theorem norm_iff_pell {a b x : ℕ} (hx : x + a = 2 * b) :
    normEleven a b ↔ x ^ 2 = 5 * a ^ 2 + 44 ∨ x ^ 2 + 44 = 5 * a ^ 2 := by
  have hs := congrArg (fun y : ℕ => y ^ 2) hx
  have hm := congrArg (fun y : ℕ => a * y) hx
  unfold normEleven
  constructor <;> rintro (h | h)
  · left; nlinarith only [h, hs, hm]
  · right; nlinarith only [h, hs, hm]
  · left; nlinarith only [h, hs, hm]
  · right; nlinarith only [h, hs, hm]

/-- Exact membership in the upper Lucas–Fibonacci diagonal by a signed Pell
equation. The congruence selects the correct orbit and encodes parity. -/
theorem exists_lucasFibonacciSum_iff_pell (y : ℕ) :
    (∃ n, y = lucasFibonacciSum n) ↔
      ∃ x : ℕ, x ≡ 7 * y [MOD 22] ∧ (x ^ 2 = 5 * y ^ 2 + 44 ∨ x ^ 2 + 44 = 5 * y ^ 2) := by
  constructor
  · rintro ⟨n, rfl⟩
    obtain ⟨_, hlt, hmod, hn⟩ := pair_properties n
    let x := 2 * lucasFibonacciSum (n + 1) - lucasFibonacciSum n
    have hx : x + lucasFibonacciSum n = 2 * lucasFibonacciSum (n + 1) := by dsimp [x]; omega
    refine ⟨x, ?_, (norm_iff_pell hx).mp hn⟩
    change _ % 11 = _ % 11 at hmod
    change _ % 22 = _ % 22
    omega
  · rintro ⟨x, hm, he⟩
    change _ % 22 = _ % 22 at hm
    have hxy : y < x := by
      by_contra! hle
      have hs := Nat.mul_self_le_mul_self hle
      have hy : y ≤ 3 := by
        by_contra! hlarge
        have hlo := Nat.mul_self_le_mul_self (show 4 ≤ y by omega)
        rcases he with h | h <;> nlinarith only [h, hs, hlo]
      interval_cases y <;> interval_cases x <;> norm_num at *
    let b := (x + y) / 2
    have hx : x + y = 2 * b := by dsimp [b]; omega
    have hmod : b ≡ 4 * y [MOD 11] := by change _ % 11 = _ % 11; omega
    obtain ⟨n, hn, _⟩ := pair_is_consecutive (by omega : y < b) ((norm_iff_pell hx).mpr he) hmod
    exact ⟨n, hn.symm⟩

/-- The original prime-values conjecture, expressed without a recurrence. -/
theorem lucasFibonacci_prime_values_iff_pell :
    (type_of% @infinitely_many_lucas_fibonacci_sum_primes) ↔
      {p : ℕ | p.Prime ∧ ∃ x : ℕ, x ≡ 7 * p [MOD 22] ∧
        (x ^ 2 = 5 * p ^ 2 + 44 ∨ x ^ 2 + 44 = 5 * p ^ 2)}.Infinite := by
  simp only [exists_lucasFibonacciSum_iff_pell]

#print axioms exists_lucasFibonacciSum_iff_pell
#print axioms lucasFibonacci_prime_values_iff_pell

end Arxiv.«2211.10788»
