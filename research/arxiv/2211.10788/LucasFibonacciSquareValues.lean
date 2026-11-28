import Mathlib
import LucasFibonacciDiagonalUnion

/-!
# Square values of the Lucas–Fibonacci diagonals

Cohn's dyadic Lucas congruences exclude further squares after comparison with
the initial square values. The final classification uses the pinned upper
sequence and the lower sequence from the neighboring-prime question.
-/

namespace Arxiv.«2211.10788»

/-- The Lucas numbers at indices `2,4,8,…`. -/
private def traceAt : ℕ → ℕ
  | 0 => 3
  | r + 1 => traceAt r * traceAt r - 2

private lemma trace_ge (r : ℕ) : 3 ≤ traceAt r := by
  induction r with
  | zero => decide
  | succ r ih =>
    simp only [traceAt]
    have : 5 ≤ traceAt r * traceAt r := by nlinarith only [ih]
    omega

private lemma trace_step (r : ℕ) : traceAt (r+1) + 2 = traceAt r * traceAt r := by
  simp only [traceAt]
  have := trace_ge r
  exact Nat.sub_add_cancel (by nlinarith)

private lemma trace_mod_four (r : ℕ) : traceAt r % 4 = 3 := by
  induction r with
  | zero => decide
  | succ r ih =>
    have h := congrArg (· % 4) (trace_step r)
    rw [Nat.mul_mod, ih] at h
    omega

private lemma trace_mod_three (r : ℕ) : traceAt (r+1) % 3 ≠ 0 := by
  induction r with
  | zero => decide
  | succ r ih =>
    have h := congrArg (· % 3) (trace_step (r+1))
    rw [Nat.mul_mod] at h
    rcases (show traceAt (r+1) % 3 = 1 ∨ traceAt (r+1) % 3 = 2 by omega) with e | e <;>
      rw [e] at h <;> omega

private lemma prime_three_factor (n : ℕ) (hn : n % 4 = 3) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  induction n using induction_on_primes with
  | zero => contradiction
  | one => contradiction
  | prime_mul p n hp ih =>
    by_cases h : p % 4 = 3
    · exact ⟨p,hp,dvd_mul_right p n,h⟩
    have h' : n % 4 = 3 := by
      rw [Nat.mul_mod] at hn
      have hp' : p % 4 < 4 := Nat.mod_lt _ (by decide)
      have hn' : n % 4 < 4 := Nat.mod_lt _ (by decide)
      interval_cases a : p % 4 <;> interval_cases b : n % 4 <;> omega
    obtain ⟨q,hq,hd,hm⟩ := ih h'
    exact ⟨q,hq,dvd_mul_of_dvd_right hd _,hm⟩

private def Recurs (s : ℕ → ℤ) : Prop := ∀ n, s (n+2) = s n + s (n+1)

/-- Cayley–Hamilton at a dyadic step, obtained by squaring the preceding step. -/
private lemma trace_shift (s : ℕ → ℤ) (hs : Recurs s) (r n : ℕ) :
    s (n + 4 * 2^r) + s n = (traceAt r : ℤ) * s (n + 2 * 2^r) := by
  induction r generalizing n with
  | zero =>
    norm_num [traceAt]
    have h0 := hs n
    have h1 := hs (n+1)
    have h2 := hs (n+2)
    linarith
  | succ r ih =>
    let d := 2^r
    have h0 := ih n
    have h1 := ih (n+2*d)
    have h2 := ih (n+4*d)
    change s (n+4*d) + s n = _ * s (n+2*d) at h0
    change s (n+2*d+4*d) + s (n+2*d) = _ * s (n+2*d+2*d) at h1
    change s (n+4*d+4*d) + s (n+4*d) = _ * s (n+4*d+2*d) at h2
    rw [show n+2*d+2*d = n+4*d by omega, show n+2*d+4*d = n+6*d by omega] at h1
    rw [show n+4*d+2*d = n+6*d by omega, show n+4*d+4*d = n+8*d by omega] at h2
    have hc : (traceAt (r+1) : ℤ) + 2 = (traceAt r : ℤ) * traceAt r := by
      exact_mod_cast trace_step r
    rw [pow_succ]
    change s (n+4*(d*2)) + s n = _ * s (n+2*(d*2))
    rw [show 4*(d*2)=8*d by omega, show 2*(d*2)=4*d by omega]
    linear_combination h2 + h0 + (traceAt r : ℤ) * h1 - s (n+4*d) * hc

private lemma signed_period (s : ℕ → ℤ) (hs : Recurs s) (r a m p : ℕ)
    (hp : p ∣ traceAt r) :
    (s (a + (4 * 2^r)*m) : ZMod p) = (-1)^m * (s a : ZMod p) := by
  have flip (t : ℕ) : (s (t+4*2^r) : ZMod p) = -(s t : ZMod p) := by
    have h := congrArg (fun z : ℤ => (z : ZMod p)) (trace_shift s hs r t)
    push_cast at h
    rw [(ZMod.natCast_eq_zero_iff ..).mpr hp, zero_mul] at h
    exact eq_neg_of_add_eq_zero_left h
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, flip, ih, pow_succ]
    ring

/-- A square anchor excludes a second square at any nonzero dyadic displacement
whose odd part reverses the sign modulo a suitable Lucas-number divisor. -/
private lemma exclude_square (s : ℕ → ℤ) (hs : Recurs s) (a root r₀ m : ℕ)
    (hanchor : s a = (root : ℤ)^2) (hm : m ≠ 0)
    (hunit : ∀ r ≥ r₀, ∀ p : ℕ, p.Prime → p % 4 = 3 → p ∣ traceAt r → ¬p ∣ root) :
    ¬ ∃ y : ℤ, s (a+(4*2^r₀)*m) = y^2 := by
  obtain ⟨j,t,ht,hmt⟩ := Nat.exists_eq_two_pow_mul_odd hm
  let r := r₀+j
  obtain ⟨p,hp,hd,hp4⟩ := prime_three_factor _ (trace_mod_four r)
  have : Fact p.Prime := ⟨hp⟩
  have hroot : (root : ZMod p) ≠ 0 :=
    mt (ZMod.natCast_eq_zero_iff ..).mp (hunit r (by dsimp [r]; omega) p hp hp4 hd)
  rintro ⟨y,hy⟩
  rw [hmt,show 4*2^r₀*(2^j*t) = 4*2^r*t by dsimp [r]; rw [pow_add]; ring] at hy
  have h := signed_period s hs r a t p hd
  rw [hy,hanchor,ht.neg_one_pow] at h
  push_cast at h
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hroot (by simpa using h) hp4

private def fibLike (a b : ℤ) : ℕ → ℤ
  | 0 => a
  | 1 => b
  | n+2 => fibLike a b n + fibLike a b (n+1)

private lemma fibLike_recurs (a b : ℤ) : Recurs (fibLike a b) := fun _ => rfl

private abbrev upperShift := fibLike 81 (-50)
private abbrev lowerShift := fibLike 9 (-5)

private lemma upper_recurs : Recurs upperShift := fibLike_recurs _ _
private lemma lower_recurs : Recurs lowerShift := fibLike_recurs _ _

private lemma upper_shifted (n : ℕ) : upperShift (n+9) = (lucasFibonacciSum n : ℤ) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h₀ h₁ =>
    rw [show n+2+9 = n+9+2 by omega, upper_recurs (n+9),
      lucas_fibonacci_sum_recurrence]
    push_cast
    change upperShift (n+9) + upperShift (n+1+9) = _
    rw [h₀,h₁,add_comm]

private lemma lower_shifted (n : ℕ) : lowerShift (n+5) = (lowerNeighborAtAddTwo n : ℤ) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h₀ h₁ =>
    have h : lowerNeighborAtAddTwo (n+2) = lowerNeighborAtAddTwo n + lowerNeighborAtAddTwo (n+1) := by
      simp only [lowerNeighborAtAddTwo,Nat.fib_add_two]; omega
    rw [show n+2+5 = n+5+2 by omega, lower_recurs (n+5),h]
    push_cast
    change lowerShift (n+5) + lowerShift (n+1+5) = _
    rw [h₀,h₁]


private lemma small_root (r₀ root : ℕ)
    (hr : root = 1 ∨ root = 2 ∨ (0 < r₀ ∧ (root = 3 ∨ root = 9))) :
    ∀ r ≥ r₀, ∀ p : ℕ, p.Prime → p % 4 = 3 → p ∣ traceAt r → ¬p ∣ root := by
  intro r hrr p hp hp4 hd
  have h2 : ¬p ∣ 2 := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
    omega
  rcases hr with rfl | rfl | ⟨hpos,hr⟩
  · exact hp.not_dvd_one
  · exact h2
  have h3 : ¬p ∣ 3 := by
    intro h
    have h' := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
    subst p
    obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by omega)
    exact trace_mod_three r (Nat.mod_eq_zero_of_dvd hd)
  rcases hr with rfl | rfl
  · exact h3
  · simpa only [show (9 : ℕ) = 3*3 by decide, hp.dvd_mul, or_self] using h3

private lemma anchor_excludes (s : ℕ → ℤ) (hs : Recurs s) (a root r₀ n : ℕ)
    (hanchor : s a = (root : ℤ)^2)
    (hr : root = 1 ∨ root = 2 ∨ (0 < r₀ ∧ (root = 3 ∨ root = 9)))
    (hlt : a < n) (hd : 4*2^r₀ ∣ n-a) : ¬∃ y : ℤ, s n = y^2 := by
  obtain ⟨m,hm⟩ := hd
  have h : n = a+(4*2^r₀)*m := by omega
  have hm0 : m ≠ 0 := by rintro rfl; simp at h; omega
  rw [h]
  exact exclude_square s hs a root r₀ m hanchor hm0 (small_root _ _ hr)

private lemma eight_period (s : ℕ → ℤ) (hs : Recurs s)
    (h₀ : (s 12 : ZMod 8) = s 0) (h₁ : (s 13 : ZMod 8) = s 1) :
    Function.Periodic (fun n => (s n : ZMod 8)) 12 := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact h₀
  | one => exact h₁
  | more n ih₀ ih₁ =>
    change (s (n+2+12) : ZMod 8) = s (n+2)
    rw [show n+2+12 = n+12+2 by omega, hs (n+12), hs n]
    push_cast
    exact congrArg₂ (· + ·) ih₀ ih₁

private lemma small_residue (s : ℕ → ℤ) (hs : Recurs s)
    (h₀ : (s 12 : ZMod 8) = s 0) (h₁ : (s 13 : ZMod 8) = s 1) (n : ℕ) :
    (s n : ZMod 8) = (s (n%12) : ZMod 8) := by
  have h := (eight_period s hs h₀ h₁).nat_mul (n/12) (n%12)
  change (s (n%12+n/12*12) : ZMod 8) = _ at h
  rwa [Nat.mul_comm (n/12), Nat.mod_add_div] at h

private lemma upper_mod_eight (n : ℕ) (hn : n % 4 = 3) : ¬∃ y : ℤ, upperShift n = y^2 := by
  rintro ⟨y,hy⟩
  have table : ∀ i : Fin 12, i.val % 4 = 3 →
      ∀ z : ZMod 8, (upperShift i.val : ZMod 8) ≠ z^2 := by decide
  have h := small_residue upperShift upper_recurs (by decide) (by decide) n
  rw [hy] at h
  push_cast at h
  exact table ⟨n%12,by omega⟩ (by dsimp; omega) (y : ZMod 8) h.symm

private lemma lower_mod_eight (n : ℕ) (hn : n % 2 = 1) : ¬∃ y : ℤ, lowerShift n = y^2 := by
  rintro ⟨y,hy⟩
  have table : ∀ i : Fin 12, i.val % 2 = 1 →
      ∀ z : ZMod 8, (lowerShift i.val : ZMod 8) ≠ z^2 := by decide
  have h := small_residue lowerShift lower_recurs (by decide) (by decide) n
  rw [hy] at h
  push_cast at h
  exact table ⟨n%12,by omega⟩ (by dsimp; omega) (y : ZMod 8) h.symm

/-- The only square values of the pinned upper diagonal are 1, 4 and 9. -/
theorem lucasFibonacciSum_isSquare_iff (n : ℕ) :
    IsSquare (lucasFibonacciSum n) ↔ n = 0 ∨ n = 1 ∨ n = 3 := by
  constructor
  · rintro ⟨y,hy⟩
    have hsq : ∃ z : ℤ, upperShift (n+9) = z^2 := by
      refine ⟨y, ?_⟩
      rw [upper_shifted,hy]; push_cast; ring
    by_contra! hn
    have drop (a root r : ℕ) (ha : upperShift a = (root : ℤ)^2)
        (hr : root = 1 ∨ root = 2 ∨ (0 < r ∧ (root = 3 ∨ root = 9)))
        (hlt : a < n+9) (hd : 4*2^r ∣ (n+9)-a) : False :=
      anchor_excludes _ upper_recurs a root r (n+9) ha hr hlt hd hsq
    rcases (show n%4 = 0 ∨ n%4 = 1 ∨ n%4 = 2 ∨ n%8 = 3 ∨ n%8 = 7 by omega) with h|h|h|h|h
    · exact drop 9 1 0 (by decide) (by decide) (by omega) (by norm_num; omega)
    · exact drop 10 2 0 (by decide) (by decide) (by omega) (by norm_num; omega)
    · exact upper_mod_eight _ (by omega) hsq
    · exact drop 12 3 1 (by decide) (by decide) (by omega) (by norm_num; omega)
    · exact drop 0 9 1 (by decide) (by decide) (by omega) (by norm_num; omega)
  · rintro (rfl | rfl | rfl)
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩

/-- At indices `n+2` the lower diagonal has just the square 81 at index 9. -/
theorem lowerNeighbor_isSquare_iff (n : ℕ) :
    IsSquare (lowerNeighborAtAddTwo n) ↔ n = 7 := by
  constructor
  · rintro ⟨y,hy⟩
    have hsq : ∃ z : ℤ, lowerShift (n+5) = z^2 := by
      refine ⟨y, ?_⟩
      rw [lower_shifted,hy]; push_cast; ring
    by_contra hn
    have drop (a root r : ℕ) (ha : lowerShift a = (root : ℤ)^2)
        (hr : root = 1 ∨ root = 2 ∨ (0 < r ∧ (root = 3 ∨ root = 9)))
        (hlt : a < n+5) (hd : 4*2^r ∣ (n+5)-a) : False :=
      anchor_excludes _ lower_recurs a root r (n+5) ha hr hlt hd hsq
    rcases (show n%2 = 0 ∨ n%4 = 1 ∨ n%8 = 3 ∨ n%8 = 7 by omega) with h|h|h|h
    · exact lower_mod_eight _ (by omega) hsq
    · exact drop 2 2 0 (by decide) (by decide) (by omega) (by norm_num; omega)
    · exact drop 0 3 1 (by decide) (by decide) (by omega) (by norm_num; omega)
    · exact drop 12 9 1 (by decide) (by decide) (by omega) (by norm_num; omega)
  · rintro rfl
    exact ⟨9,rfl⟩

/-- Cohn's two quartics of norm 44, jointly over all nonnegative coordinates. -/
theorem quartic_norm_forty_four_iff (x y : ℕ) :
    (x^2 = 5*y^4+44 ∨ x^2+44 = 5*y^4) ↔
      (x=7 ∧ y=1) ∨ (x=6 ∧ y=2) ∨ (x=19 ∧ y=3) ∨ (x=181 ∧ y=9) := by
  constructor
  · intro hn
    have hw : ∃ w : ℕ, w^2 = 5*(y^2)^2+44 ∨ w^2+44 = 5*(y^2)^2 := by
      exact ⟨x, by simpa only [← pow_mul] using hn⟩
    have hy : y^2 = 1 ∨ y^2 = 4 ∨ y^2 = 9 ∨ y^2 = 81 := by
      rcases (either_diagonal_iff_pell _).mpr hw with ⟨n, h⟩ | (h | ⟨n, h⟩)
      · have hs : IsSquare (lucasFibonacciSum n) := ⟨y,by rw [←h,pow_two]⟩
        rcases (lucasFibonacciSum_isSquare_iff n).mp hs with rfl | rfl | rfl
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
      · have : y ≤ 1 := by nlinarith
        interval_cases y <;> contradiction
      · have hs : IsSquare (lowerNeighborAtAddTwo n) := ⟨y,by rw [←h,pow_two]⟩
        obtain rfl := (lowerNeighbor_isSquare_iff n).mp hs
        exact Or.inr (Or.inr (Or.inr h))
    have rt (a b : ℕ) (h : a^2 = b) : a = Nat.sqrt b := by rw [←h,Nat.sqrt_eq']
    rcases hy with h|h|h|h
    all_goals
      have yr := rt _ _ h
      norm_num [Nat.sqrt] at yr
      subst y
      rcases hn with hn | hn
      · have xr := rt _ _ hn
        norm_num at xr
        subst x
        first | decide | exact absurd hn (by decide)
      · have hn' : x^2 = _ := Nat.eq_sub_of_add_eq hn
        have xr := rt _ _ hn'
        norm_num at xr
        subst x
        first | decide | exact absurd hn (by decide)
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> decide

/-- At each dyadic scale one prime congruent to three modulo four reverses the sign
of every Fibonacci recurrence when the index advances by four times that power of two. -/
theorem dyadic_sign_prime (r : ℕ) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ ∀ s : ℕ → ℤ,
      (∀ n, s (n+2) = s n + s (n+1)) → ∀ a m,
      (s (a+(4*2^r)*m) : ZMod p) = (-1)^m * (s a : ZMod p) := by
  obtain ⟨p,hp,hd,h4⟩ := prime_three_factor _ (trace_mod_four r)
  exact ⟨p,hp,h4,fun s hs a m => signed_period s hs r a m p hd⟩

#print axioms dyadic_sign_prime

#print axioms lucasFibonacciSum_isSquare_iff
#print axioms lowerNeighbor_isSquare_iff
#print axioms quartic_norm_forty_four_iff

end Arxiv.«2211.10788»
