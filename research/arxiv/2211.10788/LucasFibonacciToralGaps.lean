import Mathlib
import research.arxiv.«2211.10788».NeighboringLucasFibonacciPrimes

/-! Prime factors at bounded index gaps on the two neighboring Hosoya diagonals,
conditional on the trace-one case of the Toral Affine Sieve Conjecture. -/

namespace Arxiv.«2211.10788»

open Filter Matrix
open scoped Matrix

/-- A restricted consequence of Kontorovich–Lagarias, Conjecture 1.1. We use only matrices
of trace one and determinant minus one, positive integral coordinates, and an increasing
first coordinate. Any constant strictly between zero and their β₂ suffices. -/
def TraceOneToralSieveBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (A : Matrix (Fin 2) (Fin 2) ℚ) (x y : ℕ → ℕ),
    A.trace = 1 → A.det = -1 → StrictMono x → 0 < x 0 → (∀ n, 0 < y n) →
    (∀ n, A *ᵥ ![(x n : ℚ), (y n : ℚ)] = ![(x (n + 1) : ℚ), (y (n + 1) : ℚ)]) →
    ∀ᶠ n in atTop, c * Real.log (Real.log ((x n * y n : ℕ) : ℝ)) ≤
      (ArithmeticFunction.cardFactors (x n * y n) : ℝ)

/-- Two linearly independent solutions to the Fibonacci recurrence give integral
coordinates on the orbit of a rational conjugate of the Fibonacci matrix. -/
private theorem fibonacci_pair_orbit (x y : ℕ → ℕ)
    (hx : ∀ n, x (n + 2) = x (n + 1) + x n) (hy : ∀ n, y (n + 2) = y (n + 1) + y n)
    (hind : (x 0 : ℚ) * y 1 - (x 1 : ℚ) * y 0 ≠ 0) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℚ, A.trace = 1 ∧ A.det = -1 ∧
      ∀ n, A *ᵥ ![(x n : ℚ), (y n : ℚ)] = ![(x (n + 1) : ℚ), (y (n + 1) : ℚ)] := by
  let B : Matrix (Fin 2) (Fin 2) ℚ := !![x 0, x 1; y 0, y 1]
  let T : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 1, 1]
  let A := B * T * B⁻¹
  have hB : IsUnit B.det := isUnit_iff_ne_zero.mpr (by simpa [B, det_fin_two] using hind)
  have comm : A * B = B * T := B.nonsing_inv_mul_cancel_right _ hB
  have tr : A.trace = 1 := by
    dsimp only [A]
    rw [trace_mul_cycle, B.nonsing_inv_mul hB, one_mul]
    norm_num [T, trace, Fin.sum_univ_two]
  have det : A.det = -1 := by
    dsimp only [A]
    rw [det_mul_comm, ← Matrix.mul_assoc, B.nonsing_inv_mul hB, one_mul]
    norm_num [T, det_fin_two]
  let v (n : ℕ) : Fin 2 → ℚ := ![(x n : ℚ), (y n : ℚ)]
  have recV (n : ℕ) : v (n + 2) = v (n + 1) + v n := by
    ext i
    fin_cases i <;> simp [v, hx, hy]
  have act (e : Fin 2 → ℚ) : A *ᵥ (B *ᵥ e) = B *ᵥ (T *ᵥ e) := by
    rw [mulVec_mulVec, comm, mulVec_mulVec]
  have col0 : B *ᵥ ![1, 0] = v 0 := by ext i; fin_cases i <;> simp [B, v, mulVec]
  have col1 : B *ᵥ ![0, 1] = v 1 := by ext i; fin_cases i <;> simp [B, v, mulVec]
  have t0 : T *ᵥ ![1, 0] = ![0, 1] := by
    ext i; fin_cases i <;> simp [T, mulVec]
  have t1 : T *ᵥ ![0, 1] = ![0, 1] + ![1, 0] := by
    ext i; fin_cases i <;> simp [T, mulVec]
  refine ⟨A, tr, det, ?_⟩
  change ∀ n, A *ᵥ v n = v (n + 1)
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simpa only [col0, t0, col1] using act ![1, 0]
  | one => simpa only [col1, t1, mulVec_add, col0, recV 0] using act ![0, 1]
  | more n h₀ h₁ =>
    rw [recV n, mulVec_add, h₀, h₁, recV (n + 1)]

/-- The two sums at physical index m + 2. -/
inductive HosoyaNeighbor | upper | lower
  deriving DecidableEq

instance : Fintype HosoyaNeighbor :=
  ⟨{.upper, .lower}, by rintro (_ | _) <;> simp⟩

/-- Value on the chosen diagonal at physical index m + 2. -/
def HosoyaNeighbor.value : HosoyaNeighbor → ℕ → ℕ
  | .upper, m => lucasFibonacciSum (m + 2)
  | .lower, m => lowerNeighborAtAddTwo m

theorem HosoyaNeighbor.value_step (s : HosoyaNeighbor) (m : ℕ) :
    s.value (m + 2) = s.value (m + 1) + s.value m := by
  cases s with
  | upper => exact lucas_fibonacci_sum_recurrence (m + 2)
  | lower => simp only [HosoyaNeighbor.value, lowerNeighborAtAddTwo, Nat.fib_add_two]; omega

private theorem value_strict (s : HosoyaNeighbor) : StrictMono s.value := by
  apply strictMono_nat_of_lt_succ
  intro m
  cases s with
  | upper =>
    exact Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.fib_mono (by omega)))
      (Nat.fib_add_two_strictMono (by omega))
  | lower =>
    have h := Nat.fib_add_two_strictMono (Nat.lt_succ_self m)
    have h' := Nat.fib_mono (Nat.le_succ m)
    change Nat.fib m ≤ Nat.fib (m + 1) at h'
    change Nat.fib (m + 2) < Nat.fib (m + 1 + 2) at h
    change 2 * Nat.fib (m + 2) + Nat.fib m < 2 * Nat.fib (m + 1 + 2) + Nat.fib (m + 1)
    omega

private theorem value_pos (s : HosoyaNeighbor) (n : ℕ) : 0 < s.value n :=
  (show 0 < s.value 0 by cases s <;> decide).trans_le ((value_strict s).monotone n.zero_le)

/-- The determinant at shift h also obeys the recurrence in h. For all four choices
of sides it is negative at shifts two and three, hence at every larger shift. -/
theorem HosoyaNeighbor.pair_independent (s t : HosoyaNeighbor) (h : ℕ) (hd : s ≠ t ∨ 0 < h) :
    (s.value 0 : ℚ) * t.value (1 + h) - (s.value 1 : ℚ) * t.value (0 + h) ≠ 0 := by
  let D (j : ℕ) := (s.value 0 : ℚ) * t.value (j + 1) - (s.value 1 : ℚ) * t.value j
  have recD (j : ℕ) : D (j + 2) = D (j + 1) + D j := by
    dsimp only [D]
    rw [show j + 2 + 1 = (j + 1) + 2 by rfl, HosoyaNeighbor.value_step t (j + 1), HosoyaNeighbor.value_step t j]
    push_cast
    ring
  have neg (j : ℕ) : D (j + 2) < 0 := by
    induction j using Nat.twoStepInduction with
    | zero => cases s <;> cases t <;> norm_num [D, HosoyaNeighbor.value, lucasFibonacciSum, lowerNeighborAtAddTwo]
    | one => cases s <;> cases t <;> norm_num [D, HosoyaNeighbor.value, lucasFibonacciSum, lowerNeighborAtAddTwo]
    | more j h₀ h₁ => rw [recD (j + 2)]; exact add_neg h₁ h₀
  cases h with
  | zero =>
    cases s <;> cases t <;> simp_all [HosoyaNeighbor.value, lucasFibonacciSum, lowerNeighborAtAddTwo] <;> norm_num
  | succ h =>
    cases h with
    | zero => cases s <;> cases t <;> norm_num [HosoyaNeighbor.value, lucasFibonacciSum, lowerNeighborAtAddTwo]
    | succ h => rw [Nat.zero_add, Nat.add_comm 1]; exact (neg h).ne

/-- Exactly the distinct pairs of sites admit a trace-one, determinant-minus-one
rational matrix advancing their two coordinates together for every index. -/
theorem hosoya_shifted_orbit_iff (s t : HosoyaNeighbor) (h : ℕ) :
    (∃ A : Matrix (Fin 2) (Fin 2) ℚ, A.trace = 1 ∧ A.det = -1 ∧
      ∀ n, A *ᵥ ![(s.value n : ℚ), (t.value (n + h) : ℚ)] =
        ![(s.value (n + 1) : ℚ), (t.value (n + 1 + h) : ℚ)]) ↔ s ≠ t ∨ 0 < h := by
  constructor
  · rintro ⟨A, _, _, act⟩
    by_contra! he
    obtain ⟨rfl, hh⟩ := he
    obtain rfl : h = 0 := by omega
    have ratio (n : ℕ) : (A 0 0 + A 0 1) * s.value n = s.value (n + 1) := by
      simpa [mulVec, vecHead, vecTail, add_mul] using congrFun (act n) 0
    have bad : (s.value 0 : ℚ) * s.value 2 = (s.value 1 : ℚ)^2 := by
      linear_combination (s.value 1 : ℚ) * ratio 0 - (s.value 0 : ℚ) * ratio 1
    cases s <;> norm_num [HosoyaNeighbor.value, lucasFibonacciSum, lowerNeighborAtAddTwo] at bad
  · intro hd
    exact fibonacci_pair_orbit s.value (fun n => t.value (n + h)) (HosoyaNeighbor.value_step s)
      (fun n => by simpa [Nat.add_right_comm] using HosoyaNeighbor.value_step t (n + h))
      (HosoyaNeighbor.pair_independent s t h hd)

private theorem shifted_factors_tendsto (sieve : TraceOneToralSieveBound)
    (s t : HosoyaNeighbor) (h : ℕ) (hd : s ≠ t ∨ 0 < h) :
    Tendsto (fun n => ArithmeticFunction.cardFactors (s.value n * t.value (n + h))) atTop atTop := by
  let y (n : ℕ) := t.value (n + h)
  obtain ⟨A, tr, det, act⟩ := (hosoya_shifted_orbit_iff s t h).mpr hd
  obtain ⟨c, hc, bound⟩ := sieve
  have hb := bound A s.value y tr det (value_strict s) (value_pos s 0)
    (fun n => value_pos t (n + h)) act
  have grow : Tendsto (fun n => s.value n * y n) atTop atTop := by
    apply tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right _ (value_pos t (n + h)))
    exact (value_strict s).tendsto_atTop
  have logs := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp grow))
  have hh := Tendsto.const_mul_atTop hc logs
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [hb, hh.eventually_ge_atTop (k : ℝ)] with n hb' hk
  exact_mod_cast hk.trans hb'

/-- Under the toral sieve bound, every fixed-width window eventually has more than R
prime factors, counted with multiplicity, in the product at every two distinct sites. -/
theorem hosoya_window_factor_growth (sieve : TraceOneToralSieveBound) (H R : ℕ) :
    ∀ᶠ n in atTop, ∀ (s t : HosoyaNeighbor) (h : Fin (H + 1)), s ≠ t ∨ 0 < h.val →
      R < ArithmeticFunction.cardFactors (s.value n * t.value (n + h.val)) := by
  simp only [Filter.eventually_all]
  intro s t h hd
  exact (shifted_factors_tendsto sieve s t h hd).eventually_gt_atTop R

/-- Fix a window width and an upper bound for the number of prime factors of a value.
Beyond a common threshold, each such window has at most one qualifying site across
both diagonals, counting two values at the same index as distinct sites. -/
theorem hosoya_almost_prime_sites_separated (sieve : TraceOneToralSieveBound) (H K : ℕ) :
    ∃ N, ∀ (m n : ℕ) (s t : HosoyaNeighbor), N ≤ m → m ≤ n → n ≤ m + H →
      ArithmeticFunction.cardFactors (s.value m) ≤ K →
      ArithmeticFunction.cardFactors (t.value n) ≤ K → m = n ∧ s = t := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hosoya_window_factor_growth sieve H (2 * K))
  refine ⟨N, ?_⟩
  intro m n s t hm hmn hwidth hs ht
  by_contra! h
  let d : Fin (H + 1) := ⟨n - m, by omega⟩
  have hd : s ≠ t ∨ 0 < d.val := by
    dsimp [d]
    by_cases he : m = n
    · exact Or.inl (h he)
    · exact Or.inr (by omega)
  have hf := hN m hm s t d hd
  rw [show m + d.val = n by dsimp [d]; omega,
    ArithmeticFunction.cardFactors_mul (value_pos s m).ne' (value_pos t n).ne'] at hf
  omega

/-- Only finitely many m give primes on both diagonals at index m + 2, conditionally.
The index-one upper value is 4. -/
theorem finite_neighboring_prime_indices_of_toral_sieve (sieve : TraceOneToralSieveBound) :
    {m : ℕ | (lucasFibonacciSum (m + 2)).Prime ∧ (lowerNeighborAtAddTwo m).Prime}.Finite := by
  obtain ⟨N, hN⟩ := hosoya_almost_prime_sites_separated sieve 0 1
  refine (Set.finite_lt_nat N).subset ?_
  rintro m ⟨hu, hl⟩
  change m < N
  by_contra! hm
  have he := hN m m .upper .lower hm le_rfl le_rfl
    (ArithmeticFunction.cardFactors_eq_one_iff_prime.mpr hu).le
    (ArithmeticFunction.cardFactors_eq_one_iff_prime.mpr hl).le
  cases he.2

#print axioms HosoyaNeighbor.value_step
#print axioms HosoyaNeighbor.pair_independent
#print axioms hosoya_shifted_orbit_iff
#print axioms hosoya_window_factor_growth
#print axioms hosoya_almost_prime_sites_separated
#print axioms finite_neighboring_prime_indices_of_toral_sieve

end Arxiv.«2211.10788»
