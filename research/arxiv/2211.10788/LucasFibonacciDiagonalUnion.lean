import NeighboringLucasFibonacciPrimes

/-! The pooled upper and lower Lucas–Fibonacci diagonals of Ching et al.
The lower diagonal starts at index one with 3. -/

namespace Arxiv.«2211.10788»

/-- At index one the lower value is F₁ + L₀ = 3; its remaining values
are the previously defined lower neighbors at index m+2. -/
def IsLowerNeighborValue (y : ℕ) : Prop := y = 3 ∨ ∃ m, y = lowerNeighborAtAddTwo m

private theorem lower_increases : StrictMono lowerNeighborAtAddTwo := by
  apply strictMono_nat_of_lt_succ
  intro m
  have h := Nat.fib_add_two_strictMono (Nat.lt_succ_self m)
  have h' := Nat.fib_mono (Nat.le_succ m)
  simp only [lowerNeighborAtAddTwo]
  change Nat.fib m ≤ Nat.fib (m + 1) at h'
  change Nat.fib (m + 2) < Nat.fib (m + 1 + 2) at h
  omega

private theorem lower_below_upper (m : ℕ) :
    lowerNeighborAtAddTwo (m + 1) + 2 * Nat.fib m = lucasFibonacciSum (m + 2) := by
  simp only [lowerNeighborAtAddTwo, lucasFibonacciSum, Nat.fib_add_two]
  omega

private theorem upper_below_lower (m : ℕ) :
    lucasFibonacciSum m + Nat.fib (m + 1) = lowerNeighborAtAddTwo m := by
  simp only [lowerNeighborAtAddTwo, lucasFibonacciSum, Nat.fib_add_two]
  omega

/-- The two ranges share only 5, with the two indices allowed to differ. -/
theorem both_diagonals_iff_five (y : ℕ) :
    ((∃ n, y = lucasFibonacciSum n) ∧ IsLowerNeighborValue y) ↔ y = 5 := by
  constructor
  · rintro ⟨⟨n, rfl⟩, hl⟩
    rcases hl with h | ⟨m, hm⟩
    · cases n with
      | zero => norm_num [lucas_fibonacci_sum_zero] at h
      | succ n =>
        have h₀ := Nat.fib_mono (show 1 ≤ n + 1 by omega)
        have h₁ := Nat.fib_mono (show 3 ≤ n + 1 + 2 by omega)
        change 2 * Nat.fib (n + 1) + Nat.fib (n + 1 + 2) = 3 at h
        change 1 ≤ Nat.fib (n + 1) at h₀
        change 2 ≤ Nat.fib (n + 1 + 2) at h₁
        omega
    · rcases n with _ | _ | _ | i
      · have hb := lower_increases.monotone (Nat.zero_le m)
        change 2 ≤ lowerNeighborAtAddTwo m at hb
        rw [lucas_fibonacci_sum_zero] at hm
        omega
      · cases m with
        | zero => change 4 = 2 at hm; omega
        | succ m =>
          have hb := lower_increases.monotone (show 1 ≤ m + 1 by omega)
          change 5 ≤ lowerNeighborAtAddTwo (m + 1) at hb
          rw [lucas_fibonacci_sum_one] at hm
          omega
      · rfl
      · have hlo := lower_below_upper (i + 1)
        change lucasFibonacciSum (i + 3) = lowerNeighborAtAddTwo m at hm
        change lowerNeighborAtAddTwo (i + 2) + 2 * Nat.fib (i + 1) = lucasFibonacciSum (i + 3) at hlo
        have hhi := upper_below_lower (i + 3)
        have hf := Nat.fib_pos.mpr (show 0 < i + 1 by omega)
        have hg := Nat.fib_pos.mpr (show 0 < i + 3 + 1 by omega)
        rcases lt_or_ge m (i + 3) with hlt | hge
        · have := lower_increases.monotone (show m ≤ i + 2 by omega)
          omega
        · have := lower_increases.monotone hge
          omega
  · rintro rfl
    exact ⟨⟨2, rfl⟩, Or.inr ⟨1, rfl⟩⟩

private def lowerAtSucc : ℕ → ℕ
  | 0 => 3
  | m + 1 => lowerNeighborAtAddTwo m

private theorem lower_step (m : ℕ) : lowerAtSucc (m + 2) = lowerAtSucc (m + 1) + lowerAtSucc m := by
  cases m with
  | zero => decide
  | succ m =>
    simp only [lowerAtSucc, lowerNeighborAtAddTwo, Nat.fib_add_two]
    omega

private def diagonal (s : ℕ → ℕ) : Prop := s = lucasFibonacciSum ∨ s = lowerAtSucc

private theorem step {s : ℕ → ℕ} (hs : diagonal s) (m : ℕ) :
    s (m + 2) = s (m + 1) + s m := by
  rcases hs with rfl | rfl
  · exact lucas_fibonacci_sum_recurrence m
  · exact lower_step m

private def normPair (a b : ℕ) : Prop :=
  b ^ 2 = a * b + a ^ 2 + 11 ∨ b ^ 2 + 11 = a * b + a ^ 2

private theorem norm_step_both (a b : ℕ) : normPair a b ↔ normPair b (a + b) := by
  unfold normPair
  constructor <;> rintro (h | h)
  · right; nlinarith only [h]
  · left; nlinarith only [h]
  · right; nlinarith only [h]
  · left; nlinarith only [h]

private theorem classify_norm_pair {a b : ℕ} (hab : a ≤ 2 * b) (hn : normPair a b) :
    ∃ s, diagonal s ∧ ∃ n, s n = a ∧ s (n + 1) = b := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases hsmall : a ≤ 3
    · have hb : b ≤ 8 := by
        by_contra! hlarge
        obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hlarge
        rw [he] at hn
        have hm := Nat.mul_le_mul_right (9 + e) hsmall
        have hsq := Nat.mul_self_le_mul_self hsmall
        rcases hn with h | h <;> nlinarith [Nat.zero_le (e ^ 2)]
      have table : ∀ a : Fin 4, ∀ b : Fin 9, a.val ≤ 2 * b.val →
          normPair a.val b.val →
            (a.val = 1 ∧ b.val = 4) ∨ (a.val = 2 ∧ b.val = 5) ∨ (a.val = 3 ∧ b.val = 2) := by
        unfold normPair
        decide
      rcases table ⟨a, by omega⟩ ⟨b, by omega⟩ hab hn with
        ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> dsimp at ha hb <;> subst a <;> subst b
      · exact ⟨lucasFibonacciSum, Or.inl rfl, 0, rfl, rfl⟩
      · exact ⟨lowerAtSucc, Or.inr rfl, 1, rfl, rfl⟩
      · exact ⟨lowerAtSucc, Or.inr rfl, 0, rfl, rfl⟩
    · have ha4 : 4 ≤ a := by omega
      have ha2 := Nat.mul_self_le_mul_self ha4
      have hlow : a < b := by
        by_contra! hle
        have hmul := Nat.mul_le_mul_right b hle
        rcases hn with h | h <;> nlinarith only [h, ha2, hmul]
      have hhigh : b < 2 * a := by
        by_contra! hle
        obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
        rw [he] at hn
        rcases hn with h | h <;> nlinarith [Nat.zero_le (a * e)]
      let c := b - a
      have hca : c + a = b := Nat.sub_add_cancel hlow.le
      have hc : c < a := by dsimp [c]; omega
      have hn' : normPair c a := (norm_step_both c a).mpr (hca ▸ hn)
      obtain ⟨s, hs, n, he, hf⟩ := ih c hc (by omega) hn'
      refine ⟨s, hs, n + 1, hf, ?_⟩
      rw [show n + 1 + 1 = n + 2 by rfl, step hs n, hf, he]
      omega

private theorem union_iff_diagonal (y : ℕ) :
    ((∃ n, y = lucasFibonacciSum n) ∨ IsLowerNeighborValue y) ↔
      ∃ s, diagonal s ∧ ∃ n, y = s n := by
  constructor
  · rintro (hu | hₗ)
    · exact ⟨_, Or.inl rfl, hu⟩
    · rcases hₗ with h | ⟨m, h⟩
      · exact ⟨_, Or.inr rfl, 0, h⟩
      · exact ⟨_, Or.inr rfl, m + 1, h⟩
  · rintro ⟨s, hs, n, h⟩
    rcases hs with rfl | rfl
    · exact Or.inl ⟨n, h⟩
    · right
      cases n with
      | zero => exact Or.inl h
      | succ m => exact Or.inr ⟨m, h⟩

private theorem pell_from_pair {y b x : ℕ} (hx : x + y = 2 * b) :
    normPair y b ↔ x ^ 2 = 5 * y ^ 2 + 44 ∨ x ^ 2 + 44 = 5 * y ^ 2 := by
  have h₂ := congrArg (fun t : ℕ => t ^ 2) hx
  have h₃ := congrArg (y * ·) hx
  unfold normPair
  constructor <;> rintro (h | h)
  · left; nlinarith only [h, h₂, h₃]
  · right; nlinarith only [h, h₂, h₃]
  · left; nlinarith only [h, h₂, h₃]
  · right; nlinarith only [h, h₂, h₃]

private theorem stage_witness {s : ℕ → ℕ} (hs : diagonal s) (n : ℕ) :
    ∃ x, x + s n = 2 * s (n + 1) ∧
      (x ^ 2 = 5 * (s n) ^ 2 + 44 ∨ x ^ 2 + 44 = 5 * (s n) ^ 2) := by
  have hn (i : ℕ) : normPair (s i) (s (i + 1)) := by
    induction i with
    | zero => rcases hs with rfl | rfl <;> unfold normPair <;> decide
    | succ i ih =>
      rw [show i.succ + 1 = i + 2 by rfl, step hs i, add_comm (s (i + 1)) (s i)]
      exact (norm_step_both _ _).mp ih
  have he : s n ≤ 2 * s (n + 1) := by
    cases n with
    | zero => rcases hs with rfl | rfl <;> decide
    | succ n => rw [show n.succ + 1 = n + 2 by rfl, step hs n]; omega
  exact ⟨_, Nat.sub_add_cancel he, (pell_from_pair (Nat.sub_add_cancel he)).mp (hn n)⟩

private theorem realize_witness {x y : ℕ} (h : x ^ 2 = 5 * y ^ 2 + 44 ∨ x ^ 2 + 44 = 5 * y ^ 2) :
    ∃ s, diagonal s ∧ ∃ n, s n = y ∧ x + y = 2 * s (n + 1) := by
  have hp : (x : ZMod 2) = (y : ZMod 2) := by
    rcases h with he | he <;>
      have hh := congrArg (fun t : ℕ => (t : ZMod 2)) he <;>
      push_cast at hh <;>
      simpa only [show (44 : ZMod 2) = 0 by decide, show (5 : ZMod 2) = 1 by decide,
        add_zero, one_mul, ZMod.pow_card] using hh
  have hm := (ZMod.natCast_eq_natCast_iff' x y 2).mp hp
  let b := (x + y) / 2
  have hx : x + y = 2 * b := by dsimp [b]; omega
  obtain ⟨s, hs, n, he, hb⟩ := classify_norm_pair (by omega) ((pell_from_pair hx).mpr h)
  exact ⟨s, hs, n, he, hb ▸ hx⟩

/-- The unrestricted square test recognizes exactly the union of the two
neighboring diagonals, including the lower value 3 at index one. -/
theorem either_diagonal_iff_pell (y : ℕ) :
    ((∃ n, y = lucasFibonacciSum n) ∨ IsLowerNeighborValue y) ↔
      ∃ x : ℕ, x ^ 2 = 5 * y ^ 2 + 44 ∨ x ^ 2 + 44 = 5 * y ^ 2 := by
  rw [union_iff_diagonal]
  constructor
  · rintro ⟨s, hs, n, rfl⟩
    obtain ⟨x, _, h⟩ := stage_witness hs n
    exact ⟨x, h⟩
  · rintro ⟨x, h⟩
    obtain ⟨s, hs, n, he, _⟩ := realize_witness h
    exact ⟨s, hs, n, he.symm⟩

/-- The lower values are exactly the witnesses with x ≡ −7y modulo 22. -/
theorem lower_diagonal_iff_pell (y : ℕ) : IsLowerNeighborValue y ↔
    ∃ x : ℕ, 22 ∣ x + 7 * y ∧ (x ^ 2 = 5 * y ^ 2 + 44 ∨ x ^ 2 + 44 = 5 * y ^ 2) := by
  have hL (n : ℕ) : 11 ∣ lowerAtSucc (n + 1) + 3 * lowerAtSucc n := by
    induction n with
    | zero => decide
    | succ n ih =>
      rw [show n.succ + 1 = n + 2 by rfl, lower_step]
      omega
  constructor
  · intro hy
    obtain ⟨n, rfl⟩ : ∃ n, y = lowerAtSucc n := by
      rcases hy with h | ⟨m, h⟩
      · exact ⟨0, h⟩
      · exact ⟨m + 1, h⟩
    obtain ⟨x, he, hx⟩ := stage_witness (s := lowerAtSucc) (Or.inr rfl) n
    have := hL n
    exact ⟨x, by omega, hx⟩
  · rintro ⟨x, hmod, h⟩
    obtain ⟨s, hs, n, hy, hx⟩ := realize_witness h
    rcases hs with rfl | rfl
    · have hU (j : ℕ) : lucasFibonacciSum (j + 1) ≡ 4 * lucasFibonacciSum j [MOD 11] := by
        induction j with
        | zero => decide
        | succ j ih =>
          rw [show j.succ + 1 = j + 2 by rfl, lucas_fibonacci_sum_recurrence]
          change _ % 11 = _ % 11 at ih ⊢
          omega
      have hr := hU n
      change _ % 11 = _ % 11 at hr
      have hd : 11 ∣ y := by omega
      have hd' : 11 ∣ x := by omega
      obtain ⟨v, rfl⟩ := hd
      obtain ⟨w, rfl⟩ := hd'
      rcases h with h | h <;> ring_nf at h <;> omega
    · cases n with
      | zero => exact Or.inl hy.symm
      | succ m => exact Or.inr ⟨m, hy.symm⟩

/-- Infinitely many prime witnesses to the bare square test would give
infinitely many prime values on at least one of the two diagonals. -/
theorem pooled_prime_values_iff :
    {p : ℕ | p.Prime ∧ ∃ x : ℕ, x ^ 2 = 5 * p ^ 2 + 44 ∨ x ^ 2 + 44 = 5 * p ^ 2}.Infinite ↔
      (type_of% @infinitely_many_lucas_fibonacci_sum_primes) ∨
        {p : ℕ | p.Prime ∧ IsLowerNeighborValue p}.Infinite := by
  have h : {p : ℕ | p.Prime ∧ ∃ x : ℕ, x ^ 2 = 5 * p ^ 2 + 44 ∨ x ^ 2 + 44 = 5 * p ^ 2} =
      {p : ℕ | p.Prime ∧ ∃ n, p = lucasFibonacciSum n} ∪ {p : ℕ | p.Prime ∧ IsLowerNeighborValue p} := by
    ext p
    simp only [Set.mem_union, Set.mem_ofPred_eq, ← either_diagonal_iff_pell, and_or_left]
  rw [h, Set.infinite_union]

#print axioms pooled_prime_values_iff
#print axioms lower_diagonal_iff_pell
#print axioms either_diagonal_iff_pell
#print axioms both_diagonals_iff_five

end Arxiv.«2211.10788»
