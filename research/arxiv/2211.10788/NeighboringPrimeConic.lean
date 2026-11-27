import NeighboringLucasFibonacciPrimes

/-! Even-index neighboring Lucas–Fibonacci sums as the positive ordered
integer points of a quadratic equation. -/

namespace Arxiv.«2211.10788»

/-- The positive norm component of the Fibonacci recurrence consists of its
even-index pairs. Two inverse recurrence steps give a smaller first coordinate. -/
private theorem even_fibonacci_pair {a b : ℕ} (h : b ^ 2 = a * b + a ^ 2 + 1) :
    ∃ k : ℕ, Nat.fib (2 * k) = a ∧ Nat.fib (2 * k + 1) = b := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases ha : a = 0
    · subst a
      simp only [Nat.zero_mul, zero_pow (by decide : 2 ≠ 0), Nat.zero_add] at h
      have hb : b = 1 := (Nat.pow_eq_one.mp h).resolve_right (by decide)
      exact ⟨0, rfl, by simpa using hb.symm⟩
    have hab : a < b := by
      by_contra! hle
      nlinarith only [h, Nat.mul_le_mul_right b hle]
    have h2 : b ≤ 2 * a := by
      by_contra! hh
      obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (show 2 * a + 1 ≤ b by omega)
      rw [he] at h
      nlinarith [Nat.mul_self_le_mul_self (show 1 ≤ a by omega), Nat.zero_le (a * e)]
    let c := 2 * a - b
    let e := b - a
    have hca : c + e = a := by dsimp [c, e]; omega
    have hcb : c + 2 * e = b := by dsimp [c, e]; omega
    have hsmall : c < a := by dsimp [c]; omega
    have hn : e ^ 2 = c * e + c ^ 2 + 1 := by
      have h' : (c + 2 * e) ^ 2 = (c + e) * (c + 2 * e) + (c + e) ^ 2 + 1 := by
        rw [hca, hcb]; exact h
      nlinarith only [h']
    obtain ⟨k, hc, he⟩ := ih c hsmall hn
    refine ⟨k + 1, ?_, ?_⟩
    · rw [show 2 * (k + 1) = 2 * k + 2 by omega, Nat.fib_add_two, hc, he, hca]
    · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, Nat.fib_add_two,
        show 2 * k + 1 + 1 = 2 * k + 2 by rfl, Nat.fib_add_two, hc, he]
      omega

private theorem neighbor_sum (m : ℕ) :
    lowerNeighborAtAddTwo m + lucasFibonacciSum (m + 2) = 7 * Nat.fib (m + 2) := by
  simp only [lowerNeighborAtAddTwo, lucasFibonacciSum, Nat.fib_add_two]
  omega

/-- Every ordered positive point on the conic comes from an even index. -/
private theorem even_neighbors_of_conic {p q : ℕ} (hp : 0 < p) (hpq : p < q)
    (h : 11 * (p + q) ^ 2 = 49 * (p * q + 1)) :
    ∃ k : ℕ, lowerNeighborAtAddTwo (2 * k) = p ∧ lucasFibonacciSum (2 * k + 2) = q := by
  have h7 : Nat.Prime 7 := by decide
  have hv : 7 ∣ 11 * (p + q) ^ 2 := by rw [h]; exact dvd_mul_of_dvd_left (by decide) _
  have hf := h7.dvd_of_dvd_pow ((h7.dvd_mul.mp hv).resolve_left (by decide))
  obtain ⟨f, hsum⟩ := hf
  let b := q - 3 * f
  have hq : q = 3 * f + b := by dsimp [b]; omega
  have hp' : p + b = 4 * f := by omega
  have hprod : p * q + 1 = 11 * f ^ 2 := by rw [hsum] at h; nlinarith only [h]
  have hn : b ^ 2 = f * b + f ^ 2 + 1 := by
    have hh := congrArg (fun n : ℕ => n * q) hp'
    rw [hq] at hh hprod
    nlinarith only [hh, hprod]
  obtain ⟨k, h0, h1⟩ := even_fibonacci_pair hn
  cases k with
  | zero => norm_num at h0; omega
  | succ k =>
    have hf0 : Nat.fib (2 * k + 2) = f := by simpa only [Nat.mul_succ] using h0
    have hf1 : Nat.fib (2 * k + 2 + 1) = b := by simpa only [Nat.mul_succ] using h1
    have hu : lucasFibonacciSum (2 * k + 2) = q := by
      rw [lucasFibonacciSum, Nat.fib_add_two (n := 2 * k + 2), hf0, hf1]
      omega
    have hs := neighbor_sum (2 * k)
    rw [hu, hf0] at hs
    exact ⟨k, by omega, hu⟩

/-- The positive ordered points of this conic are exactly the neighboring pairs
at positive even indices. -/
theorem even_neighbors_iff_conic {p q : ℕ} (hp : 0 < p) (hpq : p < q) :
    (∃ k : ℕ, lowerNeighborAtAddTwo (2 * k) = p ∧ lucasFibonacciSum (2 * k + 2) = q) ↔
      11 * (p + q) ^ 2 = 49 * (p * q + 1) := by
  constructor
  · rintro ⟨k, rfl, rfl⟩
    have hf := lucasFibonacciSum_mul_lowerNeighbor (2 * k)
    rw [(even_two_mul k).neg_one_pow] at hf
    rw [neighbor_sum]
    zify
    nlinarith only [hf]
  · exact even_neighbors_of_conic hp hpq

/-- The two neighbors are the ordered primes p and q at some index n ≥ 2
exactly when these primes satisfy the quadratic equation. -/
theorem neighboring_prime_pair_iff_conic {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    (∃ m : ℕ, lowerNeighborAtAddTwo m = p ∧ lucasFibonacciSum (m + 2) = q) ↔
      11 * (p + q) ^ 2 = 49 * (p * q + 1) := by
  constructor
  · rintro ⟨m, rfl, rfl⟩
    have hm : Even m := by
      rcases (neighboring_primes_iff_semiprime m).mp ⟨hq, hp⟩ with h | ⟨h, _⟩
      · rw [h]; decide
      · simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rw [Nat.even_iff]; omega
    obtain ⟨k, hk⟩ := hm
    apply (even_neighbors_iff_conic hp.pos hpq).mp
    exact ⟨k, by rw [hk, two_mul], by rw [hk, two_mul]⟩
  · intro h
    obtain ⟨k, h₁, h₂⟩ := even_neighbors_of_conic hp.pos hpq h
    exact ⟨2 * k, h₁, h₂⟩

#print axioms even_neighbors_iff_conic
#print axioms neighboring_prime_pair_iff_conic

end Arxiv.«2211.10788»
